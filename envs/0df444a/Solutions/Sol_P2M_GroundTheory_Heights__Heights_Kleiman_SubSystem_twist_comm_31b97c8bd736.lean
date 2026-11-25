-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_comm_31b97c8bd736
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:11:30.297034+00:00
-- url     : https://prove2.me/submissions/3eaf56af-e29e-4bef-a3f8-7873c81478d0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg

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
open GroundTheory.Heights₂.Heights.Kleiman.SubSystem
namespace GroundTheory.Heights₂.Heights.Kleiman.SubSystem
theorem _root_.solution (F Q : SubSystem S x Ω) : F.twist Q = Q.twist F :=
  ext_sub fun I => by rw [twist_sub_eq_mul_of_line, twist_sub_eq_mul_of_line, mul_comm]
end GroundTheory.Heights₂.Heights.Kleiman.SubSystem
