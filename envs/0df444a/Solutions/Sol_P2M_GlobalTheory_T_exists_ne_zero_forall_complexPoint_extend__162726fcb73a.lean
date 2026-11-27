-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_ne_zero_forall_complexPoint_extend__162726fcb73a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:54:12.260273+00:00
-- url     : https://prove2.me/submissions/6f2d00e2-2630-428d-9988-bf733f772fc0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroForallComplexPointExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SpecialisationNumberFieldAndCountableValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroForallComplexPointExtendStatement
import Theorems.Thm_GlobalTheory_exists_ne_zero_forall_complexPoint_extend


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (B A : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [CommRing A] [IsDomain A] [Algebra B A] [Algebra.FiniteType B A], Function.Injective (algebraMap B A) → ∃ q : B, q ≠ 0 ∧ ∀ φ : B →+* ℂ, φ q ≠ 0 → ∃ ψ : A →+* ℂ, ψ.comp (algebraMap B A) = φ := by
  first | exact @GlobalTheory.exists_ne_zero_forall_complexPoint_extend | exact GlobalTheory.exists_ne_zero_forall_complexPoint_extend | (intros; apply GlobalTheory.exists_ne_zero_forall_complexPoint_extend <;> assumption)
end _root_.GlobalTheory.T
