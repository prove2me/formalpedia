-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_pow_f814712537f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:41:32.469775+00:00
-- url     : https://prove2.me/submissions/d8e32bec-b0ab-4e0f-be4f-71e1d0e09e3d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleNefPlusAmple
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_twist_944da96fb0e4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_generated_twistSys_zero__031813fa5837


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
theorem _root_.solution {Q : SubSystem S x Ω} (hQ : Q.Generated) (n : ℕ) : (Q.pow n).Generated := by
  induction n with
  | zero => exact generated_twistSys_zero'
  | succ n ih => exact KThm.generated_twist ih hQ
end KThm
end GroundTheory.Heights₂.Heights.Kleiman
