-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_sum_norm_sq_smul_e9836557e9c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:19:10.837108+00:00
-- url     : https://prove2.me/submissions/5f71e51f-92c2-4b39-82f2-d138c8e93598

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereProjectionLaw

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
open MeasureTheory ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.SphereProjectionLaw
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.SphereProjectionLaw
theorem _root_.solution (c : ℂ) (w : Fin n → ℂ) :
    ∑ j, ‖(c • w) j‖ ^ 2 = ‖c‖ ^ 2 * ∑ j, ‖w j‖ ^ 2 := by
  simp [mul_pow, Finset.mul_sum]
end GroundTheory.Heights₂.Heights.SphereProjectionLaw
