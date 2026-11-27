-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_GaussDVR_hypotheses_inhabited_3c51ba26e64f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:09:08.256039+00:00
-- url     : https://prove2.me/submissions/650377e0-9e3f-4703-9d76-fc50902fb0fd

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
namespace GaussDVR
theorem _root_.solution : (1 : MvPolynomial (Par 0 1) (𝓞 ℚ)) ≠ 0 := one_ne_zero
end GaussDVR
end GroundTheory.Heights₂.Heights.Vertical
