-- Prove2me | solution 1 for OrderClosures.isSolid_orderAdherence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:05:58.866398+00:00
-- url     : https://prove2.me/submissions/86c854d3-d3af-4b9e-81e7-432b6113d7d5

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
public import Theorems.Thm_OrderClosures_orderAdherence_eq_solidOrderAdherence

set_option autoImplicit true
@[expose] public section
public section
open Set
open OrderClosures
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
omit [VectorLattice X]
namespace OrderClosures
theorem _root_.solution {A : Set X}
    (hA : LatticeOrderedAddCommGroup.IsSolid A) :
    LatticeOrderedAddCommGroup.IsSolid (orderAdherence A) := by
  rw [orderAdherence_eq_solidOrderAdherence hA]
  exact LatticeOrderedAddCommGroup.isSolid_solidClosure (directedPositiveAdherence A)
end OrderClosures
