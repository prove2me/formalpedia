-- Prove2me | solution 1 for Preorder.IsRegularSeq.exists_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:48.62569+00:00
-- url     : https://prove2.me/submissions/f90306ca-0640-4ac1-8e69-96db4b318189

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
    {f : ℕ → Q} (hf : IsRegularSeq r f) (i N : ℕ) :
    ∃ j, N ≤ j ∧ r (f i) (f j) := by
  obtain ⟨j, hj_mem, hj_gt⟩ := (hf i).exists_gt N
  exact ⟨j, hj_gt.le, hj_mem⟩
end IsRegularSeq
end Preorder
