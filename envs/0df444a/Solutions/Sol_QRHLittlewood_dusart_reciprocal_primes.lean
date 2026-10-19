-- Prove2me | solution 1 for QRHLittlewood.dusart_reciprocal_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T21:33:40.704176+00:00
-- url     : https://prove2.me/submissions/f291aff1-2ef3-417d-82a1-ddd295a42407
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Dusart_reciprocal_primes_of_chebyshev
import Theorems.Thm_Dusart_chebyshev_theta_k2

open Real

theorem solution (x : ℝ) (hx : 10372 ≤ x) :
    (∑ p ∈ Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1)), (1 : ℝ) / p) - Real.log (Real.log x) -
        (Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) ≤
      1 / (10 * Real.log x ^ 2) + 4 / (15 * Real.log x ^ 3) :=
  Dusart.reciprocal_primes_of_chebyshev Dusart.chebyshev_theta_k2 x hx
