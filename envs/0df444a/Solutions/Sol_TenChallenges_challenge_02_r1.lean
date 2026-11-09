-- Prove2me | solution 1 for TenChallenges.challenge_02_r1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T22:51:54.565649+00:00
-- url     : https://prove2.me/submissions/825fb841-140b-46f1-aad0-8c66d7801ffa

import Definitions.Def_TenChallenges_Challenge_02

open TenChallenges in
theorem solution : statement_02 1 0 := by
  intro p m hp hm hpow
  have hp2 : 2 ≤ p := hp.out.two_le
  have hpow2 : 2 ≤ p ^ m := by
    calc 2 ≤ p := hp2
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ m := Nat.pow_le_pow_right (by omega) hm
  omega
