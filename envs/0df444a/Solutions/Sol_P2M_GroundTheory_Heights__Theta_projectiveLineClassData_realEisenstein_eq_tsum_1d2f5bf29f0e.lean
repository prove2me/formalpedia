-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_projectiveLineClassData_realEisenstein_eq_tsum_1d2f5bf29f0e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:44:22.634736+00:00
-- url     : https://prove2.me/submissions/e968b259-5026-4f5f-8c84-18f31e08f537

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
theorem _root_.solution (τ : ℍ) (s : ℝ) : realEisenstein τ s = ∑' p, eisTerm τ s p := rfl
end GroundTheory.Heights₂.Theta.projectiveLineClassData
