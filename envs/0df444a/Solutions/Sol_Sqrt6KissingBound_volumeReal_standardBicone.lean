-- Prove2me | solution 1 for Sqrt6KissingBound.volumeReal_standardBicone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:26:00.306943+00:00
-- url     : https://prove2.me/submissions/c5c012dd-f6b3-4e73-8c2f-874c10a4c33d

import Definitions.Def_Sqrt6KissingBound_BodyVolumeAdditivity
import Definitions.Def_Sqrt6KissingBound_BiconeGeometry
import Definitions.Def_Sqrt6KissingBound_LinearProfileIntegral
import Definitions.Def_Sqrt6KissingBound_ProfileIntegralReal
import Definitions.Def_Sqrt6KissingBound_BiconeVolume
import Theorems.Thm_Sqrt6KissingBound_measurableSet_upperBicone
import Theorems.Thm_Sqrt6KissingBound_volumeReal_lowerBicone
import Theorems.Thm_Sqrt6KissingBound_volumeReal_upperBicone
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_lowerBicone_disjoint_upperBicone
import Theorems.Thm_Sqrt6KissingBound_lowerBicone_subset
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
import Theorems.Thm_Sqrt6KissingBound_upperBicone_subset
import Theorems.Thm_Sqrt6KissingBound_volumeReal_union_of_subsets_ball
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.mem_tailBall
attribute [local simp] Sqrt6KissingBound.norm_standardAxis


section
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
private lemma two_power_step (k : ℕ) :
    (2 : ℝ) ^ (k + 2) = (2 : ℝ) ^ (k + 1) * 2 := by
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
end
end Sqrt6KissingBound
end

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
namespace Sqrt6KissingBound
theorem _root_.solution (k : ℕ) :
    (volume : Measure (EuclideanSpace ℝ (Fin (k + 2)))).real (standardBicone k) =
      (1 / ((k + 2) * 2 ^ (k + 1))) * unitBallVolumeReal (k + 1) := by
  rw [standardBicone, volumeReal_union_of_subsets_ball
    (lowerBicone_disjoint_upperBicone k) (measurableSet_upperBicone k)
    (fun y hy => (lowerBicone_subset k hy).2)
    (fun y hy => (upperBicone_subset k hy).2)]
  rw [volumeReal_lowerBicone, volumeReal_upperBicone]
  simp only [two_power_step, div_eq_mul_inv, mul_inv_rev]
  ring
end Sqrt6KissingBound
