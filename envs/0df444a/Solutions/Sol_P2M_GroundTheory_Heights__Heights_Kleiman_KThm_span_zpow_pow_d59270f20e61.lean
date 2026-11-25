-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KThm_span_zpow_pow_d59270f20e61
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:03:44.095976+00:00
-- url     : https://prove2.me/submissions/2d374b85-6f16-41b0-80f5-cbde4398e848

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleNefPlusAmple
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_span_zpow_mul_367f4f97d00d

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
theorem _root_.solution (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) (a : ℤ) (n : ℕ) :
    Submodule.span (chartRing S x I) {x i ^ a} ^ n =
      Submodule.span (chartRing S x I) {x i ^ (a * n)} := by
  induction n with
  | zero => simp [Submodule.one_eq_span]
  | succ n ih =>
    rw [pow_succ, ih, KThm.span_zpow_mul I hi]
    congr 3
    push_cast; ring_nf
end KThm
end GroundTheory.Heights₂.Heights.Kleiman
