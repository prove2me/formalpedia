-- Prove2me | solution 1 for Preorder.IsRegularSeq.tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:49.071145+00:00
-- url     : https://prove2.me/submissions/5e1c389e-5c21-4006-be82-13e168f04111

module
public import Mathlib.Order.WellQuasiOrder
public import Mathlib.Order.WellFoundedSet
public import Definitions.Def_LeanPool_NashWilliams_Order_WellQuasiOrder_Regular

set_option autoImplicit true
@[expose] public section
public section
open Set Preorder
noncomputable section
open Preorder
namespace Preorder
namespace IsRegularSeq
theorem _root_.solution {Q : Type*} {r : Q → Q → Prop}
    {f : ℕ → Q} (hf : IsRegularSeq r f) (k : ℕ) :
    IsRegularSeq r fun i => f (i + k) := by
  intro i
  have h_infinite : {j | r (f (i + k)) (f j)}.Infinite := hf (i + k)
  refine Set.infinite_of_forall_exists_gt fun n => ?_
  obtain ⟨j, hj₁, hj₂⟩ := h_infinite.exists_gt (n + k)
  exact ⟨j - k, by simpa [Nat.sub_add_cancel (show k ≤ j from by omega)] using hj₁,
    by omega⟩
end IsRegularSeq
end Preorder
