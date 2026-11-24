-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_KRationalDense_hypotheses_inhabited_f2ec2e0ac3ed
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T05:19:49.260804+00:00
-- url     : https://prove2.me/submissions/17fa93a9-ee0c-4d64-a489-0cf62c1f0cd2

import Mathlib


theorem solution : (0 : ℚ) < 1 / 2 ∧ (1 / 2 : ℚ) ≤ 1 := by
  norm_num
