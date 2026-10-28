-- Prove2me | solution 1 for PrivateRelease.VCLowerBound.theorem_3_11
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-28T05:58:15.275772+00:00
-- url     : https://prove2.me/submissions/5cd705ee-384e-4edb-acfe-d73d360a99b3

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.ByContra
import Theorems.Thm_PrivateRelease_VCLowerBound_theorem_3_11_explicit


namespace PrivateRelease.VCLowerBound

/-- Arithmetic end of Theorem 3.11, retaining the reconstruction failure probability. -/
theorem error_ge_one_div_128 (ε α δ : ℝ) (hε : ε ≤ 1) (hδ : δ ≤ 1 / 4)
    (h : (1 - δ) * (1 - 2 * α) ≤ Real.exp ε * (δ + 2 * α)) :
    (1 : ℝ) / 128 ≤ α := by
  by_contra! ha
  have hexp : Real.exp ε ≤ 11 / 4 := by
    have := Real.exp_le_exp.mpr hε
    have := Real.exp_one_lt_d9
    linarith
  have hfactor : 0 < 1 - 2 * α := by linarith
  have hlower : (3 / 4 : ℝ) * (1 - 2 * α) ≤ (1 - δ) * (1 - 2 * α) := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 4 - δ by linarith) hfactor.le]
  have hpos : 0 ≤ δ + 2 * α := by
    by_contra! hn
    have := mul_neg_of_pos_of_neg (Real.exp_pos ε) hn
    nlinarith
  have hupper : Real.exp ε * (δ + 2 * α) ≤ (11 / 4 : ℝ) * (δ + 2 * α) :=
    mul_le_mul_of_nonneg_right hexp hpos
  nlinarith

/-- The mission's asymptotic constant can be chosen as c = 1/32. -/
theorem explicit_to_asymptotic (ε α δ : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hδ : δ ≤ 1 / 4)
    (h : (1 - δ) * (1 - 2 * α) ≤ Real.exp ε * (δ + 2 * α)) :
    ((1 : ℝ) / 32) / (4 + 16 * ε) ≤ α := by
  have ha := error_ge_one_div_128 ε α δ hε1 hδ h
  have hd : 0 < 4 + 16 * ε := by positivity
  apply le_trans _ ha
  apply (div_le_iff₀ hd).2
  nlinarith

end PrivateRelease.VCLowerBound





open MeasureTheory PrivateRelease.VCLowerBound

-- Platform reduction through the accepted privacy/reconstruction inequality.
theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ (X : Type) (C : Set (X → Bool)) (n : ℕ) (O : Type) [MeasurableSpace O]
        (M : (Fin n → X) → Measure O) (ans : O → (X → Bool) → ℝ) (ε α δ : ℝ),
        1 ≤ n → ((2 * n : ℕ) : ℕ∞) ≤ HighDimProb.Chaining.vcDim C →
        0 ≤ ε → ε ≤ 1 → 0 < δ → δ ≤ 1 / 4 →
        (∀ z, IsProbabilityMeasure (M z)) →
        (∀ φ ∈ C, Measurable fun o => ans o φ) →
        PrivLearn.Generic.IsDP M ε → IsUseful C α δ M ans →
        c / (4 + 16 * ε) ≤ α  := by
  refine ⟨1 / 32, by norm_num, ?_⟩
  intro X C n O inst M ans ε α δ hn hvc hε0 hε1 hδ0 hδ1 hprob hans hdp huse
  apply explicit_to_asymptotic ε α δ hε0 hε1 hδ1
  exact theorem_3_11_explicit C n M ans ε α δ hn hvc hδ0 (by linarith)
    hprob hans hdp huse



#print axioms solution
