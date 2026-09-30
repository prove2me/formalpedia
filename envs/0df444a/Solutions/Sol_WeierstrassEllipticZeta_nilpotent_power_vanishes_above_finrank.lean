-- Prove2me | solution 1 for WeierstrassEllipticZeta.nilpotent_power_vanishes_above_finrank
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-10T21:36:13.510294+00:00
-- url     : https://prove2.me/submissions/61243642-25d2-4a92-898f-629825c08ff8

import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.Algebra.Algebra.Bilinear



theorem solution
    (K B : Type*) [Field K] [Ring B] [Algebra K B] [FiniteDimensional K B]
    (x : B) (hx : IsNilpotent x) :
    ∀ N : ℕ, Module.finrank K B ≤ N → x ^ N = 0 := by
  have hn : IsNilpotent (Algebra.lmul K B x) := hx.map (Algebra.lmul K B)
  have hzero : x ^ Module.finrank K B = 0 := by
    simpa only [hn.charpoly_eq_X_pow_finrank, map_pow, Polynomial.aeval_X]
      using (Algebra.aeval_self_charpoly_lmul (R := K) x)
  intro N hN
  exact pow_eq_zero_of_le hN hzero

