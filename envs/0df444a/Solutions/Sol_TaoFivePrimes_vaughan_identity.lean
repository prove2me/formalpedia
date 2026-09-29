-- Prove2me | solution 1 for TaoFivePrimes.vaughan_identity
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-13T16:15:35.956759+00:00
-- url     : https://prove2.me/submissions/7815150b-2899-477e-85b3-62fbf3deeb26

import Mathlib
import Definitions.Def_TaoFivePrimes_VaughanTruncation

open TaoFivePrimes

theorem solution (U V : ℝ) :
    TaoFivePrimes.truncLe U TaoFivePrimes.moebiusR * ArithmeticFunction.log
      - TaoFivePrimes.truncLe U TaoFivePrimes.moebiusR *
          TaoFivePrimes.truncLe V ArithmeticFunction.vonMangoldt * TaoFivePrimes.zetaR
      + TaoFivePrimes.truncGt U TaoFivePrimes.moebiusR *
          TaoFivePrimes.truncGt V ArithmeticFunction.vonMangoldt * TaoFivePrimes.zetaR
      + TaoFivePrimes.truncLe V ArithmeticFunction.vonMangoldt
      = ArithmeticFunction.vonMangoldt := by
  have hmu : truncLe U moebiusR + truncGt U moebiusR = moebiusR := truncLe_add_truncGt U _
  have hvm : truncLe V ArithmeticFunction.vonMangoldt
      + truncGt V ArithmeticFunction.vonMangoldt = ArithmeticFunction.vonMangoldt :=
    truncLe_add_truncGt V _
  have hlog : ArithmeticFunction.vonMangoldt * zetaR = ArithmeticFunction.log :=
    ArithmeticFunction.vonMangoldt_mul_zeta
  have hmz : moebiusR * zetaR = 1 := ArithmeticFunction.coe_moebius_mul_coe_zeta
  set A := truncLe U moebiusR with hA
  set B := truncGt U moebiusR with hB
  set C := truncLe V ArithmeticFunction.vonMangoldt with hC
  set D := truncGt V ArithmeticFunction.vonMangoldt with hD
  have hlog' : ArithmeticFunction.log = (C + D) * zetaR := by rw [hvm, hlog]
  calc A * ArithmeticFunction.log - A * C * zetaR + B * D * zetaR + C
      = A * ((C + D) * zetaR) - A * C * zetaR + B * D * zetaR + C := by rw [← hlog']
    _ = (A + B) * D * zetaR + C := by ring
    _ = moebiusR * D * zetaR + C := by rw [hmu]
    _ = D * (moebiusR * zetaR) + C := by ring
    _ = D + C := by rw [hmz, mul_one]
    _ = ArithmeticFunction.vonMangoldt := by rw [add_comm]; exact hvm
