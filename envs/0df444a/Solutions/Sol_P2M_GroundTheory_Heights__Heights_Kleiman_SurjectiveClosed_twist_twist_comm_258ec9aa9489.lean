-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_twist_twist_comm_258ec9aa9489
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:59:35.498857+00:00
-- url     : https://prove2.me/submissions/0e32a1c5-1535-4f44-93af-3ee951e1d3d1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_twist_sub_eq_mul_482b06edabb9

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
open GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed
theorem _root_.solution (F Q R : SubSystem S x Ω) : (F.twist Q).twist R = (F.twist R).twist Q := by
  refine SubSystem.ext_sub fun I => ?_
  rw [twist_sub_eq_mul, twist_sub_eq_mul, twist_sub_eq_mul, twist_sub_eq_mul, mul_left_comm]
end GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed
