-- Prove2me | solution 1 for OrderIdeal.mem_principal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:27:49.1328+00:00
-- url     : https://prove2.me/submissions/7593b9c8-e3b1-44cc-8226-4e9c1b572a8c

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
theorem _root_.solution {a x : X} :
    x ∈ principal a ↔ ∃ c : ℝ, 0 ≤ c ∧ |x| ≤ c • |a| := Iff.rfl
end OrderIdeal
