-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_twistMod_mul_67d3a62e5b05
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:57:26.759684+00:00
-- url     : https://prove2.me/submissions/8b5f05b6-7aa1-49b8-a550-84eff4b144a6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeAway

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
open GroundTheory.Heights₂.Heights.Kleiman.StepThree GroundTheory.Heights₂.Heights.Kleiman.StepThree.Away
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.StepThree.Away
theorem _root_.solution (a a' : ℤ) (I : Chart x) :
    twistMod S x a I * twistMod S x a' I = twistMod S x (a + a') I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  rw [twistMod_eq_span a I hi, twistMod_eq_span a' I hi, twistMod_eq_span (a + a') I hi,
    Submodule.span_mul_span, Set.singleton_mul_singleton, zpow_add₀ hxi]
end GroundTheory.Heights₂.Heights.Kleiman.StepThree.Away
