-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_projectiveLineClassData_eq_mk_5796c1fd3e82
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:50:04.330838+00:00
-- url     : https://prove2.me/submissions/8a3dc9c4-9114-45a3-980d-40d38ba06294

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_RealEisensteinNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaPeriodLatticeClassPf
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_eq_or_eq_conjugate_5f5eabf07707

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
open NumberField NumberField.InfinitePlace NumberField.ComplexEmbedding UpperHalfPlane
open scoped nonZeroDivisors ComplexConjugate
variable {K : Type} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Theta.projectiveLineClassData
theorem _root_.solution (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (w : InfinitePlace K) : w = mk σ := by
  rcases eq_or_eq_conjugate hK σ hσ w.embedding with h | h
  · rw [← mk_embedding w, h]
  · rw [← mk_embedding w, h, mk_conjugate_eq]
end GroundTheory.Heights₂.Theta.projectiveLineClassData
