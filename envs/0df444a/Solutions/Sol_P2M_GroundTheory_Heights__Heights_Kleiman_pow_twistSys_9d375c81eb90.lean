-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_pow_twistSys_9d375c81eb90
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:21:12.585241+00:00
-- url     : https://prove2.me/submissions/811cc61b-d0f1-43fc-8df5-43231bfc8634

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
theorem _root_.solution (c : ℤ) (n : ℕ) : (twistSys S x c).pow n = twistSys S x (n * c) := by
  induction n with
  | zero =>
    show twistSys S x 0 = twistSys S x (((0 : ℕ) : ℤ) * c)
    rw [Nat.cast_zero, zero_mul]
  | succ n ih =>
    change ((twistSys S x c).pow n).twist (twistSys S x c) = _
    rw [ih, twistSys_twist_eq_add]
    congr 1
    push_cast
    ring
end GroundTheory.Heights₂.Heights.Kleiman
