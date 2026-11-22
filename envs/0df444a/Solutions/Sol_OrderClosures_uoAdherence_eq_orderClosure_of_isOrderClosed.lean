-- Prove2me | solution 1 for OrderClosures.uoAdherence_eq_orderClosure_of_isOrderClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:29.910353+00:00
-- url     : https://prove2.me/submissions/06b25fda-d956-4ecd-8f19-a126d2a03737

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
public import Theorems.Thm_OrderClosures_orderAdherence_mono
public import Theorems.Thm_OrderClosures_subset_uoAdherence
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
theorem _root_.solution {Y : VectorSublattice X}
    (hY : IsOrderClosed (uoAdherence (Y : Set X))) :
    uoAdherence (Y : Set X) = orderClosure (Y : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [orderClosure]
    apply Set.mem_sInter.mpr
    intro B hB
    rcases hB with ⟨hYB, hBclosed⟩
    have hadhYB : orderAdherence (Y : Set X) ⊆ B :=
      fun _ hz ↦ hBclosed (orderAdherence_mono hYB hz)
    have hdoubleYB : orderAdherence (orderAdherence (Y : Set X)) ⊆ B :=
      fun _ hz ↦ hBclosed (orderAdherence_mono hadhYB hz)
    exact hdoubleYB ((orderAdherence_subset_uoAdherence_subset (Y := Y)).2 hx)
  · intro x hx
    rw [orderClosure] at hx
    exact Set.mem_sInter.mp hx (uoAdherence (Y : Set X))
      ⟨subset_uoAdherence (Y : Set X), hY⟩
end OrderClosures
