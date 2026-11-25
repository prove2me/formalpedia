-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_expand_69b1d82df637
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:45:31.793803+00:00
-- url     : https://prove2.me/submissions/3623acbb-6b00-423d-bb9f-6804a5b800c7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_smul_left_e39d81a0f916
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_smul_right_ded7c3f3c515
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_sum_left_11a7df46d748
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_sum_right_5baa8579accc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_eq_sum_smul_single_a55bf1f87056

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
variable {D : ℕ}
variable (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)
namespace GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
theorem _root_.solution (a b : Fin D → ℂ) :
    sesq H a b = ∑ k, ∑ l, a k * star (b l) * sesq H (Pi.single k 1) (Pi.single l 1) := by
  conv_lhs => rw [eq_sum_smul_single a, eq_sum_smul_single b]
  rw [sesq_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sesq_sum_right]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [sesq_smul_left, sesq_smul_right]
  ring
end GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
