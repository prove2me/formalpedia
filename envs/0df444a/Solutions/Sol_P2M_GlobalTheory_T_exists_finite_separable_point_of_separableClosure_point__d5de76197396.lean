-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_finite_separable_point_of_separableClosure_point__d5de76197396
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:34:29.39807+00:00
-- url     : https://prove2.me/submissions/366838c5-a3dc-4995-999a-0b210f3af880

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteSeparablePointOfSeparableClosurePoin
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteSeparablePointOfSeparableClosurePoinStatement
import Theorems.Thm_GlobalTheory_exists_finite_separable_point_of_separableClosure_point


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k B : Type) [Field k] [CommRing B] [Algebra k B], Algebra.FiniteType k B → Nonempty (B →ₐ[k] SeparableClosure k) → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧ Nonempty (B →ₐ[k] k') := by
  first | exact @GlobalTheory.exists_finite_separable_point_of_separableClosure_point | exact GlobalTheory.exists_finite_separable_point_of_separableClosure_point | (intros; apply GlobalTheory.exists_finite_separable_point_of_separableClosure_point <;> assumption)
end _root_.GlobalTheory.T
