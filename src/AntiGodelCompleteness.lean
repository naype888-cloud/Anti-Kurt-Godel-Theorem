/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez, José Arturo Nava-Hernández
-/
module

public import AntiGodelCompleteness.Monotonicity

/-!
# The closed chain: the squared mass band

`massSq d = C_N(d)² − 1`, with `C_N(d)` in closed form in `θ_d = π/(d+1)`
(`AntiGodelCompleteness.Szego`, copied from `D8_Szego.lean`). The chain closes on `π`:
`π` enters through `θ_d` and returns as the Szegő limit `π²/3 − 3`.

1. **Saturation** at `d = 2, 3`: `massSq 2 = massSq 3 = 0`.
2. **Floor** at `d = 4`: `massSq 4 = (94 − 42√5)/5 > 0`.
3. **Band** for `d ≥ 4`: `0 < massSq 4 ≤ massSq d < π²/3 − 3` (monotonicity from
   `AntiGodelCompleteness.Monotonicity`, copied from `D9_Monotonicity.lean`).
4. **Limit**: `massSq d → π²/3 − 3`, a limit that no `d` reaches; `π²/3 − 3 > 0`
   since `π > 3`.

5. **The formal system** `Sentence` of the chain (atoms on `C_M(d)`, `¬`, `∧`, `∨`, and
   `∀ d ≥ k`) is decidable, complete and consistent: `Holds φ ↔ eval φ = true`, where `eval`
   compares natural numbers only.

Every statement imports Mathlib only.

## Main results

- `Gnomon.massSq_band` : `0 < massSq 4 ≤ massSq d < π²/3 − 3` for `d ≥ 4`.
- `Gnomon.tendsto_massSq` : `massSq d → π²/3 − 3`.
- `Gnomon.closedChain` : saturation, floor, band and limit together.
- `Gnomon.Sentence.holds_iff_eval` : every sentence is decided by `eval`.
- `Gnomon.Sentence.complete`, `Gnomon.Sentence.consistent` : `φ` or `¬φ` holds, never both.
- `Gnomon.closedSystem` : the closed chain and its decidable, complete, consistent system.
-/

@[expose] public noncomputable section

open Real Filter
open scoped Topology

namespace Gnomon

/-- The squared mass `massSq d = C_M(d) = C_N(d)² − 1`. -/
def massSq (d : ℕ) : ℝ := CoherenceConstantSq d - 1

/-- The Szegő limit of the squared mass, `π²/3 − 3 = (C_N^∞)² − 1`. -/
def massSqInf : ℝ := π ^ 2 / 3 - 3

theorem massSqInf_pos : 0 < massSqInf := by
  unfold massSqInf
  nlinarith [Real.pi_gt_three]

theorem massSqInf_eq_sq : massSqInf = CoherenceConstantInf ^ 2 - 1 := by
  unfold massSqInf CoherenceConstantInf
  rw [Real.sq_sqrt (by nlinarith [Real.pi_gt_three])]
  ring

theorem massSq_two : massSq 2 = 0 := by
  simp [massSq, CoherenceConstantSq_two]

theorem massSq_three : massSq 3 = 0 := by
  simp [massSq, CoherenceConstantSq_three]

theorem massSq_four_eq : massSq 4 = (94 - 42 * √5) / 5 := by
  rw [massSq, CoherenceConstantSq_four_eq]
  ring

theorem massSq_four_pos : 0 < massSq 4 := by
  unfold massSq
  linarith [one_lt_CoherenceConstantSq_four]

/-- **The squared mass band.** For `d ≥ 4`, `0 < massSq 4 ≤ massSq d < π²/3 − 3`. -/
theorem massSq_band (d : ℕ) (hd : 4 ≤ d) :
    0 < massSq 4 ∧ massSq 4 ≤ massSq d ∧ massSq d < massSqInf := by
  refine ⟨massSq_four_pos, ?_, ?_⟩
  · unfold massSq
    have := CoherenceConstantSq_strictMonoOn_ge_four.monotoneOn (by simp) (by simpa using hd) hd
    linarith
  · have h1 := CoherenceConstant_lt_CoherenceConstantInf d hd
    have h0 : 0 ≤ CoherenceConstant d := Real.sqrt_nonneg _
    have h2 : CoherenceConstant d ^ 2 < CoherenceConstantInf ^ 2 := by nlinarith
    have hsq : CoherenceConstantSq d = CoherenceConstant d ^ 2 := by
      unfold CoherenceConstant
      rw [Real.sq_sqrt]
      linarith [one_lt_CoherenceConstantSq d hd]
    rw [massSqInf_eq_sq, massSq, hsq]
    linarith

/-- **The Szegő limit of the squared mass.** `massSq d → π²/3 − 3`. -/
theorem tendsto_massSq : Tendsto massSq atTop (𝓝 massSqInf) := by
  have h := tendsto_CoherenceConstantSq.sub_const 1
  have he : π ^ 2 / 3 - 2 - 1 = massSqInf := by unfold massSqInf; ring
  rw [he] at h
  exact h

/-- **The closed chain.** Saturation at `d = 2, 3`, the floor at `d = 4`, the band for
every `d ≥ 4`, and the Szegő limit `π²/3 − 3 > 0`. -/
theorem closedChain :
    (massSq 2 = 0 ∧ massSq 3 = 0) ∧
    massSq 4 = (94 - 42 * √5) / 5 ∧
    (∀ d, 4 ≤ d → 0 < massSq 4 ∧ massSq 4 ≤ massSq d ∧ massSq d < massSqInf) ∧
    (0 < massSqInf ∧ Tendsto massSq atTop (𝓝 massSqInf)) :=
  ⟨⟨massSq_two, massSq_three⟩, massSq_four_eq, massSq_band,
    ⟨massSqInf_pos, tendsto_massSq⟩⟩

/-! ## The four facts every sentence reduces to -/

theorem massSq_eq_zero_of_le_one {n : ℕ} (hn : n ≤ 1) : massSq (n + 2) = 0 := by
  interval_cases n
  · exact massSq_two
  · exact massSq_three

theorem massSq_pos_of_two_le {n : ℕ} (hn : 2 ≤ n) : 0 < massSq (n + 2) := by
  obtain ⟨h0, h1, -⟩ := massSq_band (n + 2) (by omega)
  linarith

theorem massSq_lt_of_lt {m n : ℕ} (hm : 2 ≤ m) (hmn : m < n) :
    massSq (m + 2) < massSq (n + 2) := by
  unfold massSq
  have := CoherenceConstantSq_strictMonoOn_ge_four (a := m + 2) (b := n + 2)
    (show 4 ≤ m + 2 by omega) (show 4 ≤ n + 2 by omega) (by omega)
  linarith

theorem massSq_lt_massSqInf (n : ℕ) : massSq (n + 2) < massSqInf := by
  rcases le_or_gt n 1 with hn | hn
  · rw [massSq_eq_zero_of_le_one hn]
    exact massSqInf_pos
  · exact (massSq_band (n + 2) (by omega)).2.2

/-! ## The formal system of the closed chain

`Sentence` is the language of the chain: atomic sentences about `C_M(d)` at the dimension
`d = n + 2`, closed under `¬`, `∧`, `∨`, together with the universal sentence
`gapFrom k : ∀ n ≥ k, 0 < C_M(n + 2)`. `Holds` is its meaning in `ℝ`; `eval` is an
algorithm on `ℕ` only. -/

/-- The sentences of the closed chain. -/
inductive Sentence where
  /-- `C_M(n + 2) = 0`. -/
  | saturates (n : ℕ)
  /-- `0 < C_M(n + 2)`. -/
  | gap (n : ℕ)
  /-- `C_M(4) ≤ C_M(n + 2) < π²/3 − 3`. -/
  | band (n : ℕ)
  /-- `C_M(n + 2) < π²/3 − 3`. -/
  | belowLimit (n : ℕ)
  /-- `C_M(m + 2) < C_M(n + 2)`. -/
  | lt (m n : ℕ)
  /-- `∀ n ≥ k, 0 < C_M(n + 2)`. -/
  | gapFrom (k : ℕ)
  | neg (φ : Sentence)
  | conj (φ ψ : Sentence)
  | disj (φ ψ : Sentence)

namespace Sentence

/-- The meaning of a sentence, a statement about real numbers. -/
def Holds : Sentence → Prop
  | saturates n => massSq (n + 2) = 0
  | gap n => 0 < massSq (n + 2)
  | band n => massSq 4 ≤ massSq (n + 2) ∧ massSq (n + 2) < massSqInf
  | belowLimit n => massSq (n + 2) < massSqInf
  | lt m n => massSq (m + 2) < massSq (n + 2)
  | gapFrom k => ∀ n, k ≤ n → 0 < massSq (n + 2)
  | neg φ => ¬ φ.Holds
  | conj φ ψ => φ.Holds ∧ ψ.Holds
  | disj φ ψ => φ.Holds ∨ ψ.Holds

/-- The decision procedure: comparisons of natural numbers only. -/
def eval : Sentence → Bool
  | saturates n => decide (n ≤ 1)
  | gap n => decide (2 ≤ n)
  | band n => decide (2 ≤ n)
  | belowLimit _ => true
  | lt m n => decide (2 ≤ n ∧ m < n)
  | gapFrom k => decide (2 ≤ k)
  | neg φ => !φ.eval
  | conj φ ψ => φ.eval && ψ.eval
  | disj φ ψ => φ.eval || ψ.eval

theorem holds_saturates_iff (n : ℕ) : (saturates n).Holds ↔ n ≤ 1 := by
  refine ⟨fun h => ?_, fun h => massSq_eq_zero_of_le_one h⟩
  by_contra hn
  exact (massSq_pos_of_two_le (by omega)).ne' h

theorem holds_gap_iff (n : ℕ) : (gap n).Holds ↔ 2 ≤ n := by
  refine ⟨fun h => ?_, massSq_pos_of_two_le⟩
  by_contra hn
  have h0 := massSq_eq_zero_of_le_one (n := n) (by omega)
  simp only [Holds, h0, lt_self_iff_false] at h

theorem holds_band_iff (n : ℕ) : (band n).Holds ↔ 2 ≤ n := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hn
    have h0 := massSq_eq_zero_of_le_one (n := n) (by omega)
    have h4 := massSq_four_pos
    simp only [Holds, h0] at h
    linarith [h.1]
  · exact ⟨(massSq_band (n + 2) (by omega)).2.1, massSq_lt_massSqInf n⟩

theorem holds_belowLimit (n : ℕ) : (belowLimit n).Holds := massSq_lt_massSqInf n

theorem holds_lt_iff (m n : ℕ) : (lt m n).Holds ↔ 2 ≤ n ∧ m < n := by
  simp only [Holds]
  rcases le_or_gt m 1 with hm | hm <;> rcases le_or_gt n 1 with hn | hn
  · rw [massSq_eq_zero_of_le_one hm, massSq_eq_zero_of_le_one hn]
    simp only [lt_self_iff_false, false_iff, not_and, not_lt]
    omega
  · rw [massSq_eq_zero_of_le_one hm]
    simp only [massSq_pos_of_two_le hn, true_iff]
    omega
  · rw [massSq_eq_zero_of_le_one hn]
    simp only [not_lt.mpr (massSq_pos_of_two_le hm).le, false_iff, not_and, not_lt]
    omega
  · constructor
    · intro h
      refine ⟨hn, ?_⟩
      by_contra hmn
      rcases (not_lt.mp hmn).lt_or_eq with hlt | heq
      · exact lt_asymm h (massSq_lt_of_lt hn hlt)
      · subst heq
        exact lt_irrefl _ h
    · exact fun h => massSq_lt_of_lt hm h.2

theorem holds_gapFrom_iff (k : ℕ) : (gapFrom k).Holds ↔ 2 ≤ k := by
  refine ⟨fun h => (holds_gap_iff k).mp (h k le_rfl), fun hk n hn => ?_⟩
  exact massSq_pos_of_two_le (by omega)

/-- **Every sentence is decided by the algorithm.** -/
theorem holds_iff_eval : ∀ φ : Sentence, φ.Holds ↔ φ.eval = true
  | saturates n => by simp [eval, holds_saturates_iff]
  | gap n => by simp [eval, holds_gap_iff]
  | band n => by simp [eval, holds_band_iff]
  | belowLimit n => by simp [eval, holds_belowLimit]
  | lt m n => by simp [eval, holds_lt_iff]
  | gapFrom k => by simp [eval, holds_gapFrom_iff]
  | neg φ => by simp [Holds, eval, holds_iff_eval φ]
  | conj φ ψ => by simp [Holds, eval, holds_iff_eval φ, holds_iff_eval ψ]
  | disj φ ψ => by simp [Holds, eval, holds_iff_eval φ, holds_iff_eval ψ]

/-- **Decidability.** The truth of every sentence is computable. -/
instance : DecidablePred Holds := fun φ => decidable_of_iff _ (holds_iff_eval φ).symm

/-- **Completeness.** Every sentence holds or its negation holds. -/
theorem complete (φ : Sentence) : φ.Holds ∨ φ.neg.Holds := by
  cases h : φ.eval
  · right
    simp [Holds, holds_iff_eval φ, h]
  · left
    exact (holds_iff_eval φ).mpr h

/-- **Consistency.** No sentence holds together with its negation. -/
theorem consistent (φ : Sentence) : ¬ (φ.Holds ∧ φ.neg.Holds) :=
  fun h => h.2 h.1

end Sentence

/-- **The closed system.** The closed chain, and its formal system: every sentence is
decided by `eval`, is complete and is consistent. -/
theorem closedSystem :
    ((massSq 2 = 0 ∧ massSq 3 = 0) ∧
      massSq 4 = (94 - 42 * √5) / 5 ∧
      (∀ d, 4 ≤ d → 0 < massSq 4 ∧ massSq 4 ≤ massSq d ∧ massSq d < massSqInf) ∧
      (0 < massSqInf ∧ Tendsto massSq atTop (𝓝 massSqInf))) ∧
    (∀ φ : Sentence, φ.Holds ↔ φ.eval = true) ∧
    (∀ φ : Sentence, φ.Holds ∨ φ.neg.Holds) ∧
    (∀ φ : Sentence, ¬ (φ.Holds ∧ φ.neg.Holds)) :=
  ⟨closedChain, Sentence.holds_iff_eval, Sentence.complete, Sentence.consistent⟩

/-! Statements about real numbers, proved by computation. -/

example : Sentence.Holds (.lt 2 5) := by decide
example : Sentence.Holds (.neg (.gap 1)) := by decide
example : Sentence.Holds (.conj (.saturates 0) (.gapFrom 2)) := by decide

end Gnomon
