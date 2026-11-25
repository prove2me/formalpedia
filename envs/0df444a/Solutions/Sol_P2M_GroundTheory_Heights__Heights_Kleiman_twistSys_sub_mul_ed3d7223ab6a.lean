-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_sub_mul_ed3d7223ab6a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:25:04.900196+00:00
-- url     : https://prove2.me/submissions/50868ea1-4041-4a13-8d49-3209532f6853

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_twist_eq_add_659a52088064

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
theorem _root_.solution (a b : ℤ) (I : Chart x) :
    (twistSys S x a).sub I * (twistSys S x b).sub I = (twistSys S x (a + b)).sub I := by
  rw [← twistSys_twist_eq_add, SubSystem.twist_sub_eq_mul_of_line, mul_comm]
end GroundTheory.Heights₂.Heights.Kleiman
