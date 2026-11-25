-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_std_norm_947a28c9cbcb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:19:08.494567+00:00
-- url     : https://prove2.me/submissions/c9fe6a40-0382-45f8-9ecf-8bfb80e91a3e

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
theorem _root_.solution (v : Fin n → ℂ) : (HermNorm.std n).norm v = √(∑ j, ‖v j‖ ^ 2) := by
  simp [HermNorm.norm, HermNorm.std]
end GroundTheory.Heights₂.Heights.SphereProjectionLaw
