-- Prove2me | solution 1 for OrderClosures.cardinalMk_le_densityCharacter_booleanStoneContinuousMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:08:41.567473+00:00
-- url     : https://prove2.me/submissions/4d6e632b-07ed-4ca8-b239-efd2598a0615

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Category.Stonean.Basic
public import Mathlib.Order.PrimeSeparator
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Definitions.Def_LeanPool_OrderClosures_Solovay
public import Theorems.Thm_OrderClosures_cardinalMk_le_densityCharacter_of_oneSeparated
public import Theorems.Thm_OrderClosures_one_le_dist_booleanStoneIndicator

set_option autoImplicit true
@[expose] public section
public section
open Set
noncomputable section
open OrderClosures
universe u v
namespace OrderClosures
theorem _root_.solution
    (B : Type u) [CompleteBooleanAlgebra B] :
    Cardinal.mk B ≤ densityCharacter C(BooleanStone B, ℝ) :=
  cardinalMk_le_densityCharacter_of_oneSeparated (booleanStoneIndicator B)
    (fun _ _ ↦ one_le_dist_booleanStoneIndicator B)
end OrderClosures
