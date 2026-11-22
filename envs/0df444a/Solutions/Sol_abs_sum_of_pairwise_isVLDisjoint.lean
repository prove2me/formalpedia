-- Prove2me | solution 1 for abs_sum_of_pairwise_isVLDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:17:43.646472+00:00
-- url     : https://prove2.me/submissions/6b5442c5-de21-4955-b2ee-941b51fd9479

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Theorems.Thm_abs_sum_finset

set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
theorem _root_.solution {n : ℕ} {x : Fin n → X} {α : Fin n → ℝ}
    (hdisj : Pairwise fun i j => IsVLDisjoint (x i) (x j)) :
    |∑ i, α i • x i| = ∑ i, |α i| • |x i| :=
  abs_sum_finset Finset.univ x α (fun _ _ _ _ hij => hdisj hij)
