-- Prove2me | solution 1 for OrderClosures.uoAdherence_eq_double_orderAdherence_and_stabilizes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:30.415506+00:00
-- url     : https://prove2.me/submissions/5f173224-c76c-4898-b86c-e3eb05e60fa5

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Pi
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_MeyerNieberg
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LatticeSeminorm
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Tactic_LLexpr
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Examples_CofK_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Hom
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Theorems.Thm_OrderClosures_subset_orderAdherence
public import Theorems.Thm_OrderClosures_orderAdherence_mono
public import Theorems.Thm_OrderClosures_orderAdherence_subset_uoAdherence_subset

set_option autoImplicit true
@[expose] public section
public section
open Set
open OrderClosures
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
namespace OrderClosures
theorem _root_.solution
    {Y : VectorSublattice X} (hY : IsOrderClosed (uoAdherence (Y : Set X))) :
    uoAdherence (Y : Set X) = orderAdherence (orderAdherence (Y : Set X)) ∧
      orderAdherence (orderAdherence (orderAdherence (Y : Set X))) =
        orderAdherence (orderAdherence (Y : Set X)) := by
  have heq : uoAdherence (Y : Set X) =
      orderAdherence (orderAdherence (Y : Set X)) := by
    apply Set.Subset.antisymm
    · exact (orderAdherence_subset_uoAdherence_subset (Y := Y)).2
    · exact fun _ hx ↦ hY (orderAdherence_mono
        (orderAdherence_subset_uoAdherence_subset (Y := Y)).1 hx)
  refine ⟨heq, ?_⟩
  calc
    orderAdherence (orderAdherence (orderAdherence (Y : Set X))) =
        orderAdherence (uoAdherence (Y : Set X)) := congrArg orderAdherence heq.symm
    _ = uoAdherence (Y : Set X) := Set.Subset.antisymm hY
      (subset_orderAdherence (uoAdherence (Y : Set X)))
    _ = orderAdherence (orderAdherence (Y : Set X)) := heq
end OrderClosures
