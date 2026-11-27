-- Prove2me | solution 1 for P2M_GlobalTheory_T_finiteDimensional_span_multilinear_values__181ef4da956c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:51:51.176151+00:00
-- url     : https://prove2.me/submissions/158eb32f-59d8-469d-a49c-000c3a6cf575

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FiniteDimensionalSpanMultilinearValues
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FiniteDimensionalSpanMultilinearValuesStatement
import Theorems.Thm_GlobalTheory_finiteDimensional_span_multilinear_values


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
theorem _root_.solution : ∀ {ι : Type} [Fintype ι] (E : ι → Type) [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)] (F : Type) [AddCommGroup F] [Module ℂ F] (T : MultilinearMap ℂ E F) (W : ∀ i, Submodule ℂ (E i)), (∀ i, FiniteDimensional ℂ (W i)) → FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ v : ∀ i, E i, (∀ i, v i ∈ W i) ∧ f = T v}) := by
  first | exact @GlobalTheory.finiteDimensional_span_multilinear_values | exact GlobalTheory.finiteDimensional_span_multilinear_values | (intros; apply GlobalTheory.finiteDimensional_span_multilinear_values <;> assumption)
end _root_.GlobalTheory.T
