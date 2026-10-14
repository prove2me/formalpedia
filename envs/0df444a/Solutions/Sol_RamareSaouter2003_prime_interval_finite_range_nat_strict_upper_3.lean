-- Prove2me | solution 3 for RamareSaouter2003.prime_interval_finite_range_nat_strict_upper
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:11:15.91176+00:00
-- url     : https://prove2.me/submissions/2bf7d932-1e6e-468a-befd-2dc9cae6f822

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_sgrp1
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_sgrp2
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_sgrp3
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_sgrp4

theorem solution (n : Nat)
    (hn : 10726905041 < n) (hupper : n <= 10 ^ (20 : Nat)) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 570899461905341 n with h2 | h2
  · -- n > 570899461905341
    rcases Nat.lt_or_ge 286750217619026779 n with h4 | h4
    · -- n > 286750217619026779
      exact RamareSaouter2003.prime_interval_nat_ladder_sgrp4 n (by omega) hupper
    · -- n <= 286750217619026779
      exact RamareSaouter2003.prime_interval_nat_ladder_sgrp3 n (by omega) (by omega)
  · -- n <= 570899461905341
    rcases Nat.lt_or_ge 2082320379773 n with h4 | h4
    · -- n > 2082320379773
      exact RamareSaouter2003.prime_interval_nat_ladder_sgrp2 n (by omega) (by omega)
    · -- n <= 2082320379773
      exact RamareSaouter2003.prime_interval_nat_ladder_sgrp1 n (by omega) (by omega)
