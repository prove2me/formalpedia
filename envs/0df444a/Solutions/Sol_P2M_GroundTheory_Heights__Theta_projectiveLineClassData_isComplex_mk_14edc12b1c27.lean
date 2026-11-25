-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_projectiveLineClassData_isComplex_mk_14edc12b1c27
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:44:00.729804+00:00
-- url     : https://prove2.me/submissions/b78c3e2e-9aeb-4338-b689-e5c2460c7441

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_RealEisensteinNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaPeriodLatticeClassPf
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul

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
omit [NumberField K]
namespace GroundTheory.Heights₂.Theta.projectiveLineClassData
theorem _root_.solution (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0) : IsComplex (mk σ) :=
  isComplex_mk_iff.mpr fun h => conjugate_ne σ hσ (ComplexEmbedding.isReal_iff.mp h)
end GroundTheory.Heights₂.Theta.projectiveLineClassData
