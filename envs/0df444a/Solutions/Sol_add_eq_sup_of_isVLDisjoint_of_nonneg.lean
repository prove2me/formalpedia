-- Prove2me | solution 1 for add_eq_sup_of_isVLDisjoint_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:39.649839+00:00
-- url     : https://prove2.me/submissions/7c60d736-b29e-40cc-8fb5-643c7556c3b3

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Theorems.Thm_inf_eq_zero_of_isVLDisjoint

set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
theorem _root_.solution {x y : X}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (h : IsVLDisjoint x y) : x + y = x ⊔ y := by
  have hinf : x ⊓ y = 0 := inf_eq_zero_of_isVLDisjoint hx hy h
  have := inf_add_sup x y
  rw [hinf, zero_add] at this
  exact this.symm
