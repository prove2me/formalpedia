-- Prove2me | solution 1 for OrderIdeal.mem_of_abs_le_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:27:29.196875+00:00
-- url     : https://prove2.me/submissions/df242686-ad45-4110-853e-d07f4b486036

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderUnit
public import Mathlib.Analysis.Normed.Group.Completeness
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Ideal
public import Theorems.Thm_VectorSublattice_abs_mem


set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open OrderIdeal
variable (J : OrderIdeal X)
namespace OrderIdeal
theorem _root_.solution {x y : X} (hx : x ∈ J)
    (h : |y| ≤ |x|) : y ∈ J :=
  J.mem_of_abs_mem (J.solid (J.abs_mem hx) (abs_nonneg y) h)
end OrderIdeal
