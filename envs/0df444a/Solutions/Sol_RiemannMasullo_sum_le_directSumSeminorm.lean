-- Prove2me | solution 1 for RiemannMasullo.sum_le_directSumSeminorm
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:26:15.812174+00:00
-- url     : https://prove2.me/submissions/631d5402-2bb7-4a23-a404-2ebfd4f1c9b0

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/ForMathlib/Analysis/Normed/Module/Seminorm/DirectSum.lean#L40-L44
import Theorems.Thm_RiemannMasullo_directSumSeminorm_apply
import Definitions.Def_RiemannMasullo_DirectSumSeminorm

open scoped DirectSum
open RiemannMasullo
variable {𝕜 ι : Type*} {X : ι → Type*}
  [NormedField 𝕜] [∀ i, AddCommGroup (X i)] [∀ i, Module 𝕜 (X i)]
  [DecidableEq ι] [∀ (i : ι) (z : X i), Decidable (z ≠ 0)]

theorem solution (p : ∀ i, Seminorm 𝕜 (X i)) (x : ⨁ i, X i)
    (s : Finset ι) : (∑ i ∈ s, p i (x i)) ≤ directSumSeminorm p x := by
  rw [directSumSeminorm_apply p x (s ∪ x.support) Finset.subset_union_right]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    (fun i _ _ ↦ apply_nonneg (p i) (x i))
