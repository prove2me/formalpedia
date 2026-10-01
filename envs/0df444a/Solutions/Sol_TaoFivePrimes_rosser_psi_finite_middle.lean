-- Prove2me | solution 1 for TaoFivePrimes.rosser_psi_finite_middle
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-24T01:05:05.954884+00:00
-- url     : https://prove2.me/submissions/16da6023-6d4e-4476-9e60-5869b2a9224c

import Theorems.Thm_TaoFivePrimes_rosser_psi_certificate_1_to_13631488
import Theorems.Thm_TaoFivePrimes_rosser_psi_certificate_13631488_to_55574528
import Theorems.Thm_TaoFivePrimes_rosser_psi_certificate_55574528_to_100000000

set_option autoImplicit false

theorem solution (n : ℕ) (hn : 1000 < n) (hN : n < 10 ^ 8) :
    Chebyshev.psi (n : ℝ) < 1.03883 * (n : ℝ) := by
  by_cases hFirst : n ≤ 13631488
  · exact TaoFivePrimes.rosser_psi_certificate_1_to_13631488.2 n hn hFirst
  by_cases hSecond : n ≤ 55574528
  · exact TaoFivePrimes.rosser_psi_certificate_13631488_to_55574528.2 n
      (by omega) hSecond
  exact TaoFivePrimes.rosser_psi_certificate_55574528_to_100000000.2 n
    (by omega) (by norm_num at hN; omega)

#print axioms solution
