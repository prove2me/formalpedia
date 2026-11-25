-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_pointForm_map_c29aef258094
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:24:55.630213+00:00
-- url     : https://prove2.me/submissions/a9c329a2-86dd-44a4-9ae8-242fd52edf24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Inhabitants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution : pointForm.map (algebraMap (𝓞 ℚ) ℚ) = X (0, 0) := by
  simp [pointForm]
end GroundTheory.Heights₂.Heights.Vertical
