-- Prove2me | solution 1 for TrulySubquadratic3SUM.threeSum_1999112
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-06T18:43:48.19855+00:00
-- url     : https://prove2.me/submissions/32ff3906-ca04-40b7-b18d-17b5dfe91a8f

import Theorems.Thm_TrulySubquadratic3SUM_threeSum_above_2249_1125
import Mathlib.Tactic.NormNum

theorem solution : EndStatement.ThreeSum.SolvedInTime 1.999112 :=
  TrulySubquadratic3SUM.threeSum_above_2249_1125 1.999112 (by norm_num)

#print axioms solution
