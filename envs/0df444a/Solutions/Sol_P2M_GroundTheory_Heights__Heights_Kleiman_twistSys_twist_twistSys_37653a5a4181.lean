-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_twist_twistSys_37653a5a4181
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:30:45.39583+00:00
-- url     : https://prove2.me/submissions/9948f31b-6cb4-4cf6-9515-4c4573285067

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem

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
theorem _root_.solution (a b : ℤ) :
    (twistSys S x a).twist (twistSys S x b) = twistSys S x (a + b) := by
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  rw [SubSystem.twist_sub_eq_mul_sub]
  change twistMod S x b I * twistMod S x a I = twistMod S x (a + b) I
  rw [twistMod_eq_span b I hi, twistMod_eq_span a I hi, twistMod_eq_span (a + b) I hi,
    Submodule.span_mul_span, Set.singleton_mul_singleton, ← zpow_add₀ hxi, add_comm b a]
end GroundTheory.Heights₂.Heights.Kleiman
