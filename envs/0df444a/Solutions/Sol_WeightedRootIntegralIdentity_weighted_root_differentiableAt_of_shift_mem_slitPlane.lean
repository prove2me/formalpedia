-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weighted_root_differentiableAt_of_shift_mem_slitPlane
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-14T14:43:56.189981+00:00
-- url     : https://prove2.me/submissions/afca212e-1ce5-4086-9a3d-3d0e8c6c1a7c

import Mathlib
open scoped BigOperators

theorem solution
    (n : ℕ) (a w : ℕ → ℝ) (z : ℂ)
    (hz : ∀ i < n, z - (a i : ℂ) ∈ Complex.slitPlane) :
    DifferentiableAt ℂ
      (fun z : ℂ =>
        ∏ i ∈ Finset.range n, (z - (a i : ℂ)) ^ (w i : ℂ)) z := by
  apply DifferentiableAt.fun_finsetProd
  intro i hi
  exact ((differentiableAt_id.sub_const (a i : ℂ)).cpow_const
    (hz i (Finset.mem_range.mp hi)))
