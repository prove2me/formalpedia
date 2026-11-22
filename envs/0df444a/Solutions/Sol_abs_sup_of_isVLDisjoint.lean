-- Prove2me | solution 1 for abs_sup_of_isVLDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:18:20.721833+00:00
-- url     : https://prove2.me/submissions/302cb7cb-d551-489a-829e-31be31293d19

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint

set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
theorem _root_.solution {x y : X} (hx : 0 ≤ x) (hy : 0 ≤ y)
    : |x ⊔ y| = |x| ⊔ |y| := by
  rw [abs_of_nonneg (le_sup_of_le_left hx), abs_of_nonneg hx, abs_of_nonneg hy]
