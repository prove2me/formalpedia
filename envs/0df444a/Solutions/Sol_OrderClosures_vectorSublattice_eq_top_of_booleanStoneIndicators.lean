-- Prove2me | solution 1 for OrderClosures.vectorSublattice_eq_top_of_booleanStoneIndicators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:09:30.608417+00:00
-- url     : https://prove2.me/submissions/fa00366e-6b35-4569-9bdc-c92c558d964d

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Category.Stonean.Basic
public import Mathlib.Order.PrimeSeparator
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Definitions.Def_LeanPool_OrderClosures_Solovay
public import Theorems.Thm_OrderClosures_isClosed_of_isOrderClosed_vectorSublattice
public import Theorems.Thm_OrderClosures_booleanStoneIndicators_separateStrongly

set_option autoImplicit true
@[expose] public section
public section
open Set
noncomputable section
open OrderClosures
universe u v
variable (B : Type u) [CompleteBooleanAlgebra B]
namespace OrderClosures
theorem _root_.solution
    (Z : VectorSublattice C(BooleanStone B, ℝ))
    (hOne : (1 : C(BooleanStone B, ℝ)) ∈ Z)
    (hIndicator : ∀ b, booleanStoneIndicator B b ∈ Z)
    (hZorder : IsOrderClosed (Z : Set C(BooleanStone B, ℝ))) :
    Z = ⊤ := by
  have hZclosed : IsClosed (Z : Set C(BooleanStone B, ℝ)) :=
    isClosed_of_isOrderClosed_vectorSublattice Z hZorder
  have hclosure : closure (Z : Set C(BooleanStone B, ℝ)) = ⊤ :=
    ContinuousMap.sublattice_closure_eq_top (Z : Set C(BooleanStone B, ℝ))
      ⟨0, Z.zero_mem⟩
      (fun f hf g hg ↦ Z.inf_mem hf hg)
      (fun f hf g hg ↦ Z.sup_mem hf hg)
      (booleanStoneIndicators_separateStrongly B Z hOne hIndicator)
  refine le_antisymm
    (show Z ≤ (⊤ : VectorSublattice C(BooleanStone B, ℝ)) from
      fun _ _ ↦ trivial) ?_
  intro f hf
  have hfclosure : f ∈ closure (Z : Set C(BooleanStone B, ℝ)) := by
    rw [hclosure]
    trivial
  rwa [hZclosed.closure_eq] at hfclosure
end OrderClosures
