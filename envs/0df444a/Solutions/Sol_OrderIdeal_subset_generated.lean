-- Prove2me | solution 1 for OrderIdeal.subset_generated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:27:46.470837+00:00
-- url     : https://prove2.me/submissions/bc368c3f-8fee-455a-8cb5-0e1158f780fe

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderUnit
public import Mathlib.Analysis.Normed.Group.Completeness
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Ideal

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open OrderIdeal
variable (J : OrderIdeal X)
namespace OrderIdeal
theorem _root_.solution (s : Set X) : s ⊆ (generated s : Set X) :=
  fun _ hx => mem_sInf.mpr (fun _ hJ => hJ hx)
end OrderIdeal
