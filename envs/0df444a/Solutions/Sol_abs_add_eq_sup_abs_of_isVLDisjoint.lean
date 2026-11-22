-- Prove2me | solution 1 for abs_add_eq_sup_abs_of_isVLDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:18:28.058595+00:00
-- url     : https://prove2.me/submissions/78a59833-b842-4c03-836f-8f82ce2de9ef

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Theorems.Thm_abs_add_of_isVLDisjoint
public import Theorems.Thm_sup_abs_eq_add_abs_of_isVLDisjoint

set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
theorem _root_.solution {x y : X}
    (h : IsVLDisjoint x y) : |x + y| = |x| ⊔ |y| := by
  rw [abs_add_of_isVLDisjoint h, sup_abs_eq_add_abs_of_isVLDisjoint h]
