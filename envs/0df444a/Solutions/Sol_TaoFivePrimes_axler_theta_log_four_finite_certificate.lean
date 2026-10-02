-- Prove2me | solution 1 for TaoFivePrimes.axler_theta_log_four_finite_certificate
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-10-01T21:38:57.315399+00:00
-- url     : https://prove2.me/submissions/703f0126-031a-4085-8afd-7ed42e721574

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_axler_chain_c1
import Theorems.Thm_TaoFivePrimes_axler_chain_c2
import Theorems.Thm_TaoFivePrimes_axler_chain_c3a
import Theorems.Thm_TaoFivePrimes_axler_chain_c3b
import Theorems.Thm_TaoFivePrimes_axler_chain_c4a1
import Theorems.Thm_TaoFivePrimes_axler_chain_c4a2
import Theorems.Thm_TaoFivePrimes_axler_chain_c4b1
import Theorems.Thm_TaoFivePrimes_axler_chain_c4b2
import Theorems.Thm_TaoFivePrimes_axler_chain_c5a1
import Theorems.Thm_TaoFivePrimes_axler_chain_c5a2
import Theorems.Thm_TaoFivePrimes_axler_chain_c5b
import Theorems.Thm_TaoFivePrimes_axler_chain_c5c
import Theorems.Thm_TaoFivePrimes_axler_chain_c6

open Finset

theorem solution (x : ℝ) (h1 : 70111 ≤ x) (h2 : x < 10 ^ 8) :
    |(∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (p : ℝ)) - x| < 100 * x / (Real.log x) ^ 4 := by
  rw [← Chebyshev.theta_eq_sum_primesLE]
  have h1s := (TaoFivePrimes.axler_chain_c1).1
  have h2s := (TaoFivePrimes.axler_chain_c2 h1s).1
  have h3s := (TaoFivePrimes.axler_chain_c3a h2s).1
  have h4s := (TaoFivePrimes.axler_chain_c3b h3s).1
  have h5s := (TaoFivePrimes.axler_chain_c4a1 h4s).1
  have h6s := (TaoFivePrimes.axler_chain_c4a2 h5s).1
  have h7s := (TaoFivePrimes.axler_chain_c4b1 h6s).1
  have h8s := (TaoFivePrimes.axler_chain_c4b2 h7s).1
  have h9s := (TaoFivePrimes.axler_chain_c5a1 h8s).1
  have h10s := (TaoFivePrimes.axler_chain_c5a2 h9s).1
  have h11s := (TaoFivePrimes.axler_chain_c5b h10s).1
  have h12s := (TaoFivePrimes.axler_chain_c5c h11s).1
  have r2 := (TaoFivePrimes.axler_chain_c2 h1s).2
  have r3 := (TaoFivePrimes.axler_chain_c3a h2s).2
  have r4 := (TaoFivePrimes.axler_chain_c3b h3s).2
  have r5 := (TaoFivePrimes.axler_chain_c4a1 h4s).2
  have r6 := (TaoFivePrimes.axler_chain_c4a2 h5s).2
  have r7 := (TaoFivePrimes.axler_chain_c4b1 h6s).2
  have r8 := (TaoFivePrimes.axler_chain_c4b2 h7s).2
  have r9 := (TaoFivePrimes.axler_chain_c5a1 h8s).2
  have r10 := (TaoFivePrimes.axler_chain_c5a2 h9s).2
  have r11 := (TaoFivePrimes.axler_chain_c5b h10s).2
  have r12 := (TaoFivePrimes.axler_chain_c5c h11s).2
  have r13 := (TaoFivePrimes.axler_chain_c6 h12s).2
  by_cases hx1 : x < (154970 : ℝ)
  · exact TaoFivePrimes.axler_chain_c1.2 x h1 hx1
  by_cases hx2 : x < (1699362 : ℝ)
  · exact r2 x (not_lt.mp hx1) hx2
  by_cases hx3 : x < (8409485 : ℝ)
  · exact r3 x (not_lt.mp hx2) hx3
  by_cases hx4 : x < (17387265 : ℝ)
  · exact r4 x (not_lt.mp hx3) hx4
  by_cases hx5 : x < (25762666 : ℝ)
  · exact r5 x (not_lt.mp hx4) hx5
  by_cases hx6 : x < (34129386 : ℝ)
  · exact r6 x (not_lt.mp hx5) hx6
  by_cases hx7 : x < (42496200 : ℝ)
  · exact r7 x (not_lt.mp hx6) hx7
  by_cases hx8 : x < (52597756 : ℝ)
  · exact r8 x (not_lt.mp hx7) hx8
  by_cases hx9 : x < (60984648 : ℝ)
  · exact r9 x (not_lt.mp hx8) hx9
  by_cases hx10 : x < (69355435 : ℝ)
  · exact r10 x (not_lt.mp hx9) hx10
  by_cases hx11 : x < (77727216 : ℝ)
  · exact r11 x (not_lt.mp hx10) hx11
  by_cases hx12 : x < (87458565 : ℝ)
  · exact r12 x (not_lt.mp hx11) hx12
  by_cases hx13 : x < (100000000 : ℝ)
  · exact r13 x (not_lt.mp hx12) hx13
  · norm_num at h2
    exact absurd h2 hx13
