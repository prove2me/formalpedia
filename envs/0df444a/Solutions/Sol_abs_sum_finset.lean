-- Prove2me | solution 1 for abs_sum_finset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:16:53.390818+00:00
-- url     : https://prove2.me/submissions/bdcd119b-4104-4dcf-b61c-f4cc5ab24d6f

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Theorems.Thm_abs_add_of_isVLDisjoint
public import Theorems.Thm_isVLDisjoint_finset_sum
public import Theorems.Thm_IsVLDisjoint_smul_left
public import Theorems.Thm_IsVLDisjoint_smul_right
public import Theorems.Thm_P2M_abs_smul__56c684b926d9


set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
theorem _root_.solution {ι : Type*} (s : Finset ι) (x : ι → X) (α : ι → ℝ)
    (hdisj : (s : Set ι).Pairwise fun i j => IsVLDisjoint (x i) (x j)) :
    |∑ i ∈ s, α i • x i| = ∑ i ∈ s, |α i| • |x i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hdisj_s : (s : Set ι).Pairwise fun i j => IsVLDisjoint (x i) (x j) := by
      intro i hi j hj hij
      exact hdisj (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj) hij
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hdisj_head : IsVLDisjoint (α a • x a) (∑ i ∈ s, α i • x i) := by
      apply isVLDisjoint_finset_sum
      intro i hi
      have hne_ai : a ≠ i := fun h => ha (h ▸ hi)
      exact ((hdisj (Finset.mem_insert_self a s)
        (Finset.mem_insert_of_mem hi) hne_ai).smul_left (α a)).smul_right (α i)
    rw [abs_add_of_isVLDisjoint hdisj_head, abs_smul', ih hdisj_s]
