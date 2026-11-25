-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KThm_span_zpow_mul_367f4f97d00d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:58:19.705853+00:00
-- url     : https://prove2.me/submissions/80ba071a-91d1-433b-8617-41b67829db47

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
theorem _root_.solution (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) (a b : ℤ) :
    Submodule.span (chartRing S x I) {x i ^ a} * Submodule.span (chartRing S x I) {x i ^ b} =
      Submodule.span (chartRing S x I) {x i ^ (a + b)} := by
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton, ← zpow_add₀ hxi]
end KThm
end GroundTheory.Heights₂.Heights.Kleiman
