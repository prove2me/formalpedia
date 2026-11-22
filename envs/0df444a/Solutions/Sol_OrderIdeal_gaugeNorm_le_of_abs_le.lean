-- Prove2me | solution 1 for OrderIdeal.gaugeNorm_le_of_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:27:39.421086+00:00
-- url     : https://prove2.me/submissions/c2188eea-d07c-4268-8c52-7dec1f86c8d6

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
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
variable (a : X)
namespace OrderIdeal
theorem _root_.solution {x : X} {c : ℝ} (hc : 0 ≤ c)
    (h : |x| ≤ c • |a|) : gaugeNorm a x ≤ c :=
  csInf_le ⟨0, fun _ ⟨hd, _⟩ => hd⟩ ⟨hc, h⟩
end OrderIdeal
