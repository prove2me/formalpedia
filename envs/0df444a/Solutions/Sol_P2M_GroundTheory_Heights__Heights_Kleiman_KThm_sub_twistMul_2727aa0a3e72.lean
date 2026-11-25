-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KThm_sub_twistMul_2727aa0a3e72
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:01:47.539964+00:00
-- url     : https://prove2.me/submissions/319f240c-dc7f-4cb7-b40e-534fb9ae5f80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleNefPlusAmple
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_sub_pow_a678e760a862

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
theorem _root_.solution (M : SubSystem S x Ω) (p : ℕ) (m : ℤ) (I : Chart x) {i : Fin (N + 1)}
    (hi : i ∈ I.1) :
    (twistMul M p m).sub I = M.sub I ^ p * Submodule.span (chartRing S x I) {x i ^ m} := by
  rw [twistMul, KThm.sub_twist, KThm.sub_pow, mul_comm]
  change _ * twistMod S x m I = _
  rw [twistMod_eq_span m I hi]
end KThm
end GroundTheory.Heights₂.Heights.Kleiman
