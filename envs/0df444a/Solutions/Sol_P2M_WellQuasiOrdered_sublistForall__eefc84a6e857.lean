-- Prove2me | solution 1 for P2M_WellQuasiOrdered_sublistForall__eefc84a6e857
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:06.560184+00:00
-- url     : https://prove2.me/submissions/c1d69406-1f5b-456c-b01f-93d7f1d3d68f

module
public import Mathlib.Order.WellQuasiOrder
public import Mathlib.Order.WellFoundedSet
public import Definitions.Def_LeanPool_NashWilliams_Order_WellQuasiOrder_Regular

set_option autoImplicit true
@[expose] public section
public section
open Set Preorder
noncomputable section
namespace WellQuasiOrdered
theorem _root_.solution {Q : Type*} {r : Q → Q → Prop} [IsPreorder Q r]
    (h : WellQuasiOrdered r) : WellQuasiOrdered (List.SublistForall₂ r) := by
  rw [← partiallyWellOrderedOn_univ_iff] at h ⊢
  simpa [Set.eq_univ_iff_forall] using h.partiallyWellOrderedOn_sublistForall₂ r
end WellQuasiOrdered
