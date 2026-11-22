-- Prove2me | solution 1 for OrderIdeal.toSubmodule_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:27:42.692346+00:00
-- url     : https://prove2.me/submissions/7a082c52-60d1-41ab-9a26-9057bf5c3ae8

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderUnit
public import Mathlib.Analysis.Normed.Group.Completeness
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Ideal
public import Theorems.Thm_VectorSublattice_toSubmodule_injective


set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open OrderIdeal
variable (J : OrderIdeal X)
namespace OrderIdeal
theorem _root_.solution :
    Function.Injective
      (fun J : OrderIdeal X => J.toSubmodule) := by
  intro p q h
  cases p; cases q; congr
  exact VectorSublattice.toSubmodule_injective h
end OrderIdeal
