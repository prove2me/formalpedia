-- Prove2me | solution 1 for RadGauss.Structural.theorem_12_part_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T12:06:57.704075+00:00
-- url     : https://prove2.me/submissions/695c1891-4b18-454a-83e0-6a8a2e4d10c7

import Mathlib
import Definitions.Def_RadGauss_RiskBound_rademacherComplexity

open MeasureTheory
open scoped ENNReal Pointwise

theorem radGauss_emp_smul_96ae {X : Type*} (n : ℕ) (F : Set (X → ℝ)) (c : ℝ) (x : Fin n → X) :
    RadGauss.RiskBound.empiricalRademacher n (c • F) x
      = ENNReal.ofReal |c| * RadGauss.RiskBound.empiricalRademacher n F x := by
  have key : ∀ σ : Fin n → Bool,
      (⨆ g ∈ F, ENNReal.ofReal |(2 / (n : ℝ)) * ∑ i, RadGauss.RiskBound.signVal (σ i) * (c * g (x i))|)
        = ENNReal.ofReal |c| *
          ⨆ g ∈ F, ENNReal.ofReal |(2 / (n : ℝ)) * ∑ i, RadGauss.RiskBound.signVal (σ i) * g (x i)| := by
    intro σ
    rw [ENNReal.mul_iSup]
    refine iSup_congr fun g => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_congr fun _ => ?_
    rw [← ENNReal.ofReal_mul (abs_nonneg c), ← abs_mul]
    congr 2
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  unfold RadGauss.RiskBound.empiricalRademacher
  rw [← Set.image_smul]
  simp_rw [iSup_image, Pi.smul_apply, smul_eq_mul, key]
  rw [← Finset.mul_sum, mul_left_comm]

open MeasureTheory Pointwise in
theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) (F : Set (X → ℝ)) (c : ℝ) :
    RadGauss.RiskBound.rademacherComplexity μ n (c • F) = ENNReal.ofReal |c| * RadGauss.RiskBound.rademacherComplexity μ n F := by
  unfold RadGauss.RiskBound.rademacherComplexity
  simp_rw [radGauss_emp_smul_96ae]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
