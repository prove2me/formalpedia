-- Prove2me | solution 1 for OrderIdeal.generated_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:27:38.367838+00:00
-- url     : https://prove2.me/submissions/6711793b-eef6-4022-9ea1-6cfd47396575

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
theorem _root_.solution {s : Set X} {J : OrderIdeal X} (h : s ⊆ (J : Set X)) :
    generated s ≤ J :=
  fun _ hx => mem_sInf.mp hx J h
end OrderIdeal
