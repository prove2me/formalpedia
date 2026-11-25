-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_assoc_e501c3cc2859
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:10:58.055208+00:00
-- url     : https://prove2.me/submissions/1740b1cc-a021-47ff-8708-395796b04902

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
theorem _root_.solution (F P Q : SubSystem S x Ω) : (F.twist P).twist Q = F.twist (P.twist Q) :=
  ext_sub fun I => by simp only [twist_sub_eq_mul_of_line, mul_assoc]
end GroundTheory.Heights₂.Heights.Kleiman.SubSystem
