-- Prove2me | solution 1 for TongString.riemannZeta_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T14:39:13.844298+00:00
-- url     : https://prove2.me/submissions/f37346f2-23fe-482f-a20e-d17d74a04088

import Mathlib

theorem solution : riemannZeta (-1) = -1 / 12 := by
  have h := riemannZeta_neg_nat_eq_bernoulli 1
  norm_num at h
  rw [h]
  ring
