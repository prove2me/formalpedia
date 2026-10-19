-- Prove2me | solution 1 for QuantumMC.MeanEst.lemma_4_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T17:55:07.557271+00:00
-- url     : https://prove2.me/submissions/5862cf11-c25a-48c5-ab3a-db2826bc56a7

import Mathlib
import Definitions.Def_QuantumMC_MeanEst_Setting

open MeasureTheory ProbabilityTheory Filter
open QuantumMC.MeanEst

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : MemLp X 2 P)
    (hpos : ∀ ω, 0 ≤ X ω) (k : ℕ) :
    (∫ ω, truncGe ((2 : ℝ) ^ k) X ω ∂P) ≤
      l2norm P X ^ 2 / (2 : ℝ) ^ k := by
  have hc : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hsq : l2norm P X ^ 2 = ∫ ω, X ω ^ 2 ∂P := by
    rw [l2norm, Real.sq_sqrt (integral_nonneg (fun ω => sq_nonneg (X ω)))]
  rw [hsq]
  have hgi : Integrable (fun ω => X ω ^ 2 / (2 : ℝ) ^ k) P :=
    (hX.integrable_sq).div_const _
  have hpt : ∀ ω, truncGe ((2 : ℝ) ^ k) X ω ≤ X ω ^ 2 / (2 : ℝ) ^ k := by
    intro ω
    by_cases h : (2 : ℝ) ^ k ≤ X ω
    · rw [truncGe, if_pos h]
      rw [le_div_iff₀ hc]
      nlinarith [mul_le_mul_of_nonneg_left h (hpos ω)]
    · rw [truncGe, if_neg h]
      positivity
  calc (∫ ω, truncGe ((2 : ℝ) ^ k) X ω ∂P)
      ≤ ∫ ω, X ω ^ 2 / (2 : ℝ) ^ k ∂P := by
        refine integral_mono_of_nonneg
          (f := fun ω => truncGe ((2 : ℝ) ^ k) X ω)
          (g := fun ω => X ω ^ 2 / (2 : ℝ) ^ k) ?_ hgi ?_
        · exact Eventually.of_forall (fun ω => by
            simp only [truncGe]; split
            · exact hpos ω
            · exact le_refl 0)
        · exact Eventually.of_forall hpt
    _ = (∫ ω, X ω ^ 2 ∂P) / (2 : ℝ) ^ k := by rw [integral_div]
