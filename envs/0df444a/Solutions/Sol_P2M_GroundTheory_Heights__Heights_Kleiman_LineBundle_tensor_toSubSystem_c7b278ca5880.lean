-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_tensor_toSubSystem_c7b278ca5880
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:27:58.054426+00:00
-- url     : https://prove2.me/submissions/2ce60bfb-e933-494d-8864-fe332e5f3490

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace LineBundle
theorem _root_.solution (L L' : LineBundle S x) :
    (L.tensor L').toSubSystem = L.toSubSystem.twist L'.toSubSystem := rfl
end LineBundle
end GroundTheory.Heights₂.Heights.Kleiman
