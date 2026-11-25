-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KThm_lbPow_toSubSystem_1a6630de4309
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:13:16.134272+00:00
-- url     : https://prove2.me/submissions/d08cb195-31b2-4f56-b2ef-0df257b6c05a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleNefPlusAmple

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
namespace KThm
theorem _root_.solution (Q : LineBundle S x) (n : ℕ) :
    (KThm.lbPow Q n).toSubSystem = Q.toSubSystem.pow n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (KThm.lbPow Q n).toSubSystem.twist Q.toSubSystem = (Q.toSubSystem.pow n).twist Q.toSubSystem
    rw [ih]
end KThm
end GroundTheory.Heights₂.Heights.Kleiman
