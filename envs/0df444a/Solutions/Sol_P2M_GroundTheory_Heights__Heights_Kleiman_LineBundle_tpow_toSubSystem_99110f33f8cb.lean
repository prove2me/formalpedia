-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_tpow_toSubSystem_99110f33f8cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:28:04.646981+00:00
-- url     : https://prove2.me/submissions/a35ea23c-1143-4308-a60d-650e145cd5e3

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
theorem _root_.solution (L : LineBundle S x) (n : ℕ) :
    (L.tpow n).toSubSystem = L.toSubSystem.pow n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((L.tpow n).toSubSystem).twist L.toSubSystem = _
    rw [ih]
    rfl
end LineBundle
end GroundTheory.Heights₂.Heights.Kleiman
