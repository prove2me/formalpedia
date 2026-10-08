-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weighted_root_div_differentiableAt_of_im_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-14T14:54:19.978494+00:00
-- url     : https://prove2.me/submissions/98ace775-9366-4ee0-bfd9-4144949fb706

import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_differentiableAt_of_shift_mem_slitPlane
open scoped BigOperators

theorem solution
    (n : ℕ) (a w : ℕ → ℝ) (z : ℂ)
    (hz : z.im ≠ 0) :
    DifferentiableAt ℂ
      (fun z : ℂ =>
        (∏ i ∈ Finset.range n, (z - (a i : ℂ)) ^ (w i : ℂ)) / z) z := by
  have hF : DifferentiableAt ℂ
      (fun z : ℂ => ∏ i ∈ Finset.range n,
        (z - (a i : ℂ)) ^ (w i : ℂ)) z := by
    apply WeightedRootIntegralIdentity.weighted_root_differentiableAt_of_shift_mem_slitPlane
    intro i hi
    rw [Complex.mem_slitPlane_iff]
    right
    simpa using hz
  have hz0 : z ≠ 0 := by
    intro h
    apply hz
    simp [h]
  exact hF.div differentiableAt_id hz0
