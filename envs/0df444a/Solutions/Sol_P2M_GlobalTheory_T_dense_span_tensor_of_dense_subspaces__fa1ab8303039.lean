-- Prove2me | solution 1 for P2M_GlobalTheory_T_dense_span_tensor_of_dense_subspaces__fa1ab8303039
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:33:51.995724+00:00
-- url     : https://prove2.me/submissions/18f6f1b9-75db-49dc-a2d4-6013d58945f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DenseSpanTensorOfDenseSubspaces
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DenseSpanTensorOfDenseSubspacesStatement
import Theorems.Thm_GlobalTheory_dense_span_tensor_of_dense_subspaces


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {ι : Type} [Fintype ι] {H : ι → Type} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] (u : (∀ i, H i) → Hs) (W : ∀ i, Submodule ℂ (H i)), (∀ x y, ⟪u x, u y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ) → Dense (Submodule.span ℂ (Set.range u) : Set Hs) → (∀ i, Dense (W i : Set (H i))) → Dense (Submodule.span ℂ (Set.range (fun x : (∀ i, W i) => u (fun i => (x i : H i)))) : Set Hs) := by
  first | exact @GlobalTheory.dense_span_tensor_of_dense_subspaces | exact GlobalTheory.dense_span_tensor_of_dense_subspaces | (intros; apply GlobalTheory.dense_span_tensor_of_dense_subspaces <;> assumption)
end _root_.GlobalTheory.T
