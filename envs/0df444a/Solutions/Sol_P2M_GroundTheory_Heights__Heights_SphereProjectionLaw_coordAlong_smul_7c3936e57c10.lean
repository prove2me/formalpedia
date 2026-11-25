-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_coordAlong_smul_7c3936e57c10
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:18:47.727522+00:00
-- url     : https://prove2.me/submissions/6fb3e8ba-2089-4bf6-98f5-b3145aa45859

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
theorem _root_.solution (p w : Fin n → ℂ) (c : ℂ) :
    coordAlong p (c • w) = c * coordAlong p w := by
  simp [coordAlong, Finset.mul_sum, mul_assoc]
end GroundTheory.Heights₂.Heights.SphereProjectionLaw
