-- Prove2me | solution 1 for PermanentRollout.subtreeCoefficientTotal_branch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/d789926f-b65f-4617-8639-136866cb17cc

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_subtreeCoefficient_branch_right
import Theorems.Thm_PermanentRollout_subtreeCoefficient_branch_left

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (lam : ℂ) {left right : BlockTree ι}
    (hdisj : Disjoint left.leaves right.leaves) :
    subtreeCoefficientTotal lam (.branch left right) =
      (1 + lam) * subtreeCoefficientTotal lam left *
        subtreeCoefficientTotal lam right := by
  change
    (∑ i ∈ left.leaves ∪ right.leaves,
      subtreeCoefficient lam (.branch left right) i) =
      (1 + lam) * subtreeCoefficientTotal lam left *
        subtreeCoefficientTotal lam right
  rw [Finset.sum_union hdisj]
  have hleft :
      (∑ i ∈ left.leaves,
        subtreeCoefficient lam (.branch left right) i) =
        lam * subtreeCoefficientTotal lam right *
          subtreeCoefficientTotal lam left := by
    calc
      (∑ i ∈ left.leaves,
        subtreeCoefficient lam (.branch left right) i) =
          ∑ i ∈ left.leaves,
            lam * subtreeCoefficientTotal lam right *
              subtreeCoefficient lam left i := by
                apply Finset.sum_congr rfl
                intro i hi
                exact subtreeCoefficient_branch_left lam hdisj hi
      _ = lam * subtreeCoefficientTotal lam right *
          subtreeCoefficientTotal lam left := by
            rw [← Finset.mul_sum]
            rfl
  have hright :
      (∑ i ∈ right.leaves,
        subtreeCoefficient lam (.branch left right) i) =
        subtreeCoefficientTotal lam left *
          subtreeCoefficientTotal lam right := by
    calc
      (∑ i ∈ right.leaves,
        subtreeCoefficient lam (.branch left right) i) =
          ∑ i ∈ right.leaves,
            subtreeCoefficientTotal lam left *
              subtreeCoefficient lam right i := by
                apply Finset.sum_congr rfl
                intro i hi
                exact subtreeCoefficient_branch_right lam hdisj hi
      _ = subtreeCoefficientTotal lam left *
          subtreeCoefficientTotal lam right := by
            rw [← Finset.mul_sum]
            rfl
  rw [hleft, hright]
  ring
end PermanentRollout
