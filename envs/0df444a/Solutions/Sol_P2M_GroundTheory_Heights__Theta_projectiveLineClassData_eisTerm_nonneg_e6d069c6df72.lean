-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_projectiveLineClassData_eisTerm_nonneg_e6d069c6df72
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:43.337302+00:00
-- url     : https://prove2.me/submissions/60b7895f-8e14-4363-9d92-8579c2fcb0f8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DedekindZetaEqSumRealEisenstein

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.projectiveLineClassData
open NumberField UpperHalfPlane
open scoped nonZeroDivisors
namespace GroundTheory.Heights₂.Theta.projectiveLineClassData
theorem _root_.solution (τ : ℍ) (s : ℝ) (p : ℤ × ℤ) : 0 ≤ eisTerm τ s p := by
  unfold eisTerm
  split_ifs
  · exact le_rfl
  · exact div_nonneg (Real.rpow_nonneg τ.im_pos.le _) (Real.rpow_nonneg (norm_nonneg _) _)
end GroundTheory.Heights₂.Theta.projectiveLineClassData
