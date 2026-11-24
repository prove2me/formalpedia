-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_sum_add_pi_single_one_3a9c5801f689
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T01:29:33.093836+00:00
-- url     : https://prove2.me/submissions/a061d911-09fb-459e-8ac3-f538b92e772b

import Mathlib
variable {K : Type} [Fintype K] [DecidableEq K]


theorem solution (m : K → ℕ) (k : K) :
    ∑ j, (m + Pi.single k 1 : K → ℕ) j = ∑ j, m j + 1 := by
  simp [Finset.sum_add_distrib,Pi.single_apply]
