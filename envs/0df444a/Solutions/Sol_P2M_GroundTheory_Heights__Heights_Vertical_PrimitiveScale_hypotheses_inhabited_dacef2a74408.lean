-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_PrimitiveScale_hypotheses_inhabited_dacef2a74408
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:09:36.411225+00:00
-- url     : https://prove2.me/submissions/9a7efef4-623f-4166-8cf7-46dec3f324ee

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
namespace PrimitiveScale
theorem _root_.solution : (X 0 : MvPolynomial (Fin 1) ℚ) ≠ 0 := X_ne_zero 0
end PrimitiveScale
end GroundTheory.Heights₂.Heights.Vertical
