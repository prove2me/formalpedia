-- Prove2me | solution 1 for PermanentRollout.subtreeFormProduct_eq_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/f98be15d-c0bb-4195-b1f8-1d7221a2dd69

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_BlockTree_disjoint_leaves_of_nodup
import Theorems.Thm_PermanentRollout_subtreeCoefficient_branch_right
import Theorems.Thm_PermanentRollout_subtreeCoefficient_branch_left
import Theorems.Thm_PermanentRollout_subtree_weighted_sum_mul_block_sum_pow
import Theorems.Thm_PermanentRollout_subtree_topProduct_union_erase_left
import Theorems.Thm_PermanentRollout_subtree_topProduct_union_erase_right

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {R ι : Type*} [CommSemiring R] [Algebra ℂ R] [DecidableEq ι]
    (y : ι → R) (t d : ℕ) (hd : d ≤ t) (lam : ℂ)
    (tree : BlockTree ι) (hnodup : tree.leafList.Nodup)
    (hnil : ∀ i ∈ tree.leaves, y i ^ (t + 1) = 0) :
    subtreeFormProduct y t d lam tree =
      ∑ i ∈ tree.leaves,
        algebraMap ℂ R (subtreeCoefficient lam tree i) *
          (y i ^ (t - d) * ∏ j ∈ tree.leaves.erase i, y j ^ t) := by
  induction tree with
  | leaf i =>
      simp [subtreeFormProduct, subtreeCoefficient]
  | branch left right ih_left ih_right =>
      have hparts := List.nodup_append.mp hnodup
      have hdisj := BlockTree.disjoint_leaves_of_nodup hnodup
      have hnil_left : ∀ i ∈ left.leaves, y i ^ (t + 1) = 0 := by
        intro i hi
        exact hnil i (Finset.mem_union_left _ hi)
      have hnil_right : ∀ i ∈ right.leaves, y i ^ (t + 1) = 0 := by
        intro i hi
        exact hnil i (Finset.mem_union_right _ hi)
      have hleft_expansion := ih_left hparts.1 hnil_left
      have hright_expansion := ih_right hparts.2.1 hnil_right
      have hleft_fill :
          (∑ i ∈ left.leaves,
            algebraMap ℂ R (subtreeCoefficient lam left i) *
              (y i ^ (t - d) * ∏ j ∈ left.leaves.erase i, y j ^ t)) *
              (∑ j ∈ left.leaves, y j) ^ d =
            algebraMap ℂ R (subtreeCoefficientTotal lam left) *
              ∏ j ∈ left.leaves, y j ^ t := by
        simpa [subtreeCoefficientTotal, map_sum] using
          subtree_weighted_sum_mul_block_sum_pow
            left.leaves y
            (fun i => algebraMap ℂ R (subtreeCoefficient lam left i))
            t d hd hnil_left
      have hright_fill :
          (∑ i ∈ right.leaves,
            algebraMap ℂ R (subtreeCoefficient lam right i) *
              (y i ^ (t - d) * ∏ j ∈ right.leaves.erase i, y j ^ t)) *
              (∑ j ∈ right.leaves, y j) ^ d =
            algebraMap ℂ R (subtreeCoefficientTotal lam right) *
              ∏ j ∈ right.leaves, y j ^ t := by
        simpa [subtreeCoefficientTotal, map_sum] using
          subtree_weighted_sum_mul_block_sum_pow
            right.leaves y
            (fun i => algebraMap ℂ R (subtreeCoefficient lam right i))
            t d hd hnil_right
      have hsum_left :
          (∑ i ∈ left.leaves,
            algebraMap ℂ R
              (subtreeCoefficient lam (.branch left right) i) *
              (y i ^ (t - d) *
                ∏ j ∈ (left.leaves ∪ right.leaves).erase i, y j ^ t)) =
            (algebraMap ℂ R lam *
              algebraMap ℂ R (subtreeCoefficientTotal lam right) *
              (∏ j ∈ right.leaves, y j ^ t)) *
              (∑ i ∈ left.leaves,
                algebraMap ℂ R (subtreeCoefficient lam left i) *
                  (y i ^ (t - d) *
                    ∏ j ∈ left.leaves.erase i, y j ^ t)) := by
        calc
          (∑ i ∈ left.leaves,
            algebraMap ℂ R
              (subtreeCoefficient lam (.branch left right) i) *
              (y i ^ (t - d) *
                ∏ j ∈ (left.leaves ∪ right.leaves).erase i, y j ^ t)) =
              ∑ i ∈ left.leaves,
                (algebraMap ℂ R lam *
                  algebraMap ℂ R (subtreeCoefficientTotal lam right) *
                  (∏ j ∈ right.leaves, y j ^ t)) *
                  (algebraMap ℂ R (subtreeCoefficient lam left i) *
                    (y i ^ (t - d) *
                      ∏ j ∈ left.leaves.erase i, y j ^ t)) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [subtreeCoefficient_branch_left lam hdisj hi,
                    subtree_topProduct_union_erase_left
                      left.leaves right.leaves hdisj y t hi]
                  simp only [map_mul]
                  ring
          _ = _ := by rw [Finset.mul_sum]
      have hsum_right :
          (∑ i ∈ right.leaves,
            algebraMap ℂ R
              (subtreeCoefficient lam (.branch left right) i) *
              (y i ^ (t - d) *
                ∏ j ∈ (left.leaves ∪ right.leaves).erase i, y j ^ t)) =
            (algebraMap ℂ R (subtreeCoefficientTotal lam left) *
              (∏ j ∈ left.leaves, y j ^ t)) *
              (∑ i ∈ right.leaves,
                algebraMap ℂ R (subtreeCoefficient lam right i) *
                  (y i ^ (t - d) *
                    ∏ j ∈ right.leaves.erase i, y j ^ t)) := by
        calc
          (∑ i ∈ right.leaves,
            algebraMap ℂ R
              (subtreeCoefficient lam (.branch left right) i) *
              (y i ^ (t - d) *
                ∏ j ∈ (left.leaves ∪ right.leaves).erase i, y j ^ t)) =
              ∑ i ∈ right.leaves,
                (algebraMap ℂ R (subtreeCoefficientTotal lam left) *
                  (∏ j ∈ left.leaves, y j ^ t)) *
                  (algebraMap ℂ R (subtreeCoefficient lam right i) *
                    (y i ^ (t - d) *
                      ∏ j ∈ right.leaves.erase i, y j ^ t)) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [subtreeCoefficient_branch_right lam hdisj hi,
                    subtree_topProduct_union_erase_right
                      left.leaves right.leaves hdisj y t hi]
                  simp only [map_mul]
                  ring
          _ = _ := by rw [Finset.mul_sum]
      calc
        subtreeFormProduct y t d lam (.branch left right) =
            (∑ i ∈ left.leaves,
              algebraMap ℂ R (subtreeCoefficient lam left i) *
                (y i ^ (t - d) * ∏ j ∈ left.leaves.erase i, y j ^ t)) *
            (∑ i ∈ right.leaves,
              algebraMap ℂ R (subtreeCoefficient lam right i) *
                (y i ^ (t - d) * ∏ j ∈ right.leaves.erase i, y j ^ t)) *
              ((∑ i ∈ left.leaves, y i) ^ d +
                algebraMap ℂ R lam *
                  (∑ i ∈ right.leaves, y i) ^ d) := by
                    rw [subtreeFormProduct_branch,
                      hleft_expansion, hright_expansion]
        _ =
            ((∑ i ∈ left.leaves,
              algebraMap ℂ R (subtreeCoefficient lam left i) *
                (y i ^ (t - d) * ∏ j ∈ left.leaves.erase i, y j ^ t)) *
              (∑ i ∈ left.leaves, y i) ^ d) *
              (∑ i ∈ right.leaves,
                algebraMap ℂ R (subtreeCoefficient lam right i) *
                  (y i ^ (t - d) * ∏ j ∈ right.leaves.erase i, y j ^ t)) +
            algebraMap ℂ R lam *
              (∑ i ∈ left.leaves,
                algebraMap ℂ R (subtreeCoefficient lam left i) *
                  (y i ^ (t - d) * ∏ j ∈ left.leaves.erase i, y j ^ t)) *
              ((∑ i ∈ right.leaves,
                algebraMap ℂ R (subtreeCoefficient lam right i) *
                  (y i ^ (t - d) * ∏ j ∈ right.leaves.erase i, y j ^ t)) *
                (∑ i ∈ right.leaves, y i) ^ d) := by ring
        _ =
            (algebraMap ℂ R (subtreeCoefficientTotal lam left) *
              (∏ j ∈ left.leaves, y j ^ t)) *
              (∑ i ∈ right.leaves,
                algebraMap ℂ R (subtreeCoefficient lam right i) *
                  (y i ^ (t - d) * ∏ j ∈ right.leaves.erase i, y j ^ t)) +
            algebraMap ℂ R lam *
              (∑ i ∈ left.leaves,
                algebraMap ℂ R (subtreeCoefficient lam left i) *
                  (y i ^ (t - d) * ∏ j ∈ left.leaves.erase i, y j ^ t)) *
              (algebraMap ℂ R (subtreeCoefficientTotal lam right) *
                ∏ j ∈ right.leaves, y j ^ t) := by
                  rw [hleft_fill, hright_fill]
        _ =
            (∑ i ∈ left.leaves,
              algebraMap ℂ R
                (subtreeCoefficient lam (.branch left right) i) *
                (y i ^ (t - d) *
                  ∏ j ∈ (left.leaves ∪ right.leaves).erase i, y j ^ t)) +
            (∑ i ∈ right.leaves,
              algebraMap ℂ R
                (subtreeCoefficient lam (.branch left right) i) *
                (y i ^ (t - d) *
                  ∏ j ∈ (left.leaves ∪ right.leaves).erase i, y j ^ t)) := by
                    rw [hsum_left, hsum_right]
                    ring
        _ =
            ∑ i ∈ (left.leaves ∪ right.leaves),
              algebraMap ℂ R
                (subtreeCoefficient lam (.branch left right) i) *
                (y i ^ (t - d) *
                  ∏ j ∈ (left.leaves ∪ right.leaves).erase i, y j ^ t) :=
                    (Finset.sum_union hdisj).symm
end PermanentRollout
