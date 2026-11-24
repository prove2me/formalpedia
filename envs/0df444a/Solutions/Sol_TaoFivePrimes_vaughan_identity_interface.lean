-- Prove2me | solution 1 for TaoFivePrimes.vaughan_identity_interface
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-21T09:23:53.376979+00:00
-- url     : https://prove2.me/submissions/ebac8438-cdf7-4704-8926-447e1e822c24

import Theorems.Thm_TaoFivePrimes_typeIExpansion_three_bilinear_sums
open ArithmeticFunction Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius BigOperators
namespace TaoFivePrimes
@[simp] theorem arithmeticRestrictLE_apply (B n : ℕ) (f : ArithmeticFunction ℝ) :
    arithmeticRestrictLE B f n = if n ≤ B then f n else 0 := rfl
@[simp] theorem arithmeticRestrictGT_apply (B n : ℕ) (f : ArithmeticFunction ℝ) :
    arithmeticRestrictGT B f n = if B < n then f n else 0 := rfl
theorem restrictLE_add_restrictGT (B : ℕ) (f : ArithmeticFunction ℝ) :
    arithmeticRestrictLE B f + arithmeticRestrictGT B f = f := by
  ext n
  rw [ArithmeticFunction.add_apply]
  by_cases h : n ≤ B
  · simp [h]
  · have h2 : B < n := Nat.lt_of_not_ge h
    simp [h, h2]
theorem vaughan_identity_interface (U V : ℕ) :
    arithmeticRestrictLE U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log
      - arithmeticRestrictLE U (μ : ArithmeticFunction ℝ) *
          arithmeticRestrictLE V ArithmeticFunction.vonMangoldt *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
      + arithmeticRestrictGT U (μ : ArithmeticFunction ℝ) *
          arithmeticRestrictGT V ArithmeticFunction.vonMangoldt *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
      + arithmeticRestrictLE V ArithmeticFunction.vonMangoldt
      = ArithmeticFunction.vonMangoldt := by
  have hmu : arithmeticRestrictLE U (μ : ArithmeticFunction ℝ) +
      arithmeticRestrictGT U (μ : ArithmeticFunction ℝ) = (μ : ArithmeticFunction ℝ) :=
    restrictLE_add_restrictGT U _
  have hvm : arithmeticRestrictLE V ArithmeticFunction.vonMangoldt +
      arithmeticRestrictGT V ArithmeticFunction.vonMangoldt = ArithmeticFunction.vonMangoldt :=
    restrictLE_add_restrictGT V _
  have hlog : ArithmeticFunction.vonMangoldt * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
      ArithmeticFunction.log := ArithmeticFunction.vonMangoldt_mul_zeta
  have hmz : (μ : ArithmeticFunction ℝ) * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) = 1 :=
    ArithmeticFunction.coe_moebius_mul_coe_zeta
  set A := arithmeticRestrictLE U (μ : ArithmeticFunction ℝ) with hA
  set B := arithmeticRestrictGT U (μ : ArithmeticFunction ℝ) with hB
  set C := arithmeticRestrictLE V ArithmeticFunction.vonMangoldt with hC
  set D := arithmeticRestrictGT V ArithmeticFunction.vonMangoldt with hD
  have hlog' : ArithmeticFunction.log = (C + D) * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) := by
    rw [hvm, hlog]
  calc A * ArithmeticFunction.log - A * C * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
        + B * D * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) + C
      = A * ((C + D) * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))
          - A * C * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
          + B * D * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) + C := by rw [← hlog']
    _ = (A + B) * D * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) + C := by ring
    _ = (μ : ArithmeticFunction ℝ) * D * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) + C := by rw [hmu]
    _ = D * ((μ : ArithmeticFunction ℝ) * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) + C := by ring
    _ = D + C := by rw [hmz, mul_one]
    _ = ArithmeticFunction.vonMangoldt := by rw [add_comm]; exact hvm
end TaoFivePrimes
open TaoFivePrimes
theorem solution (U V : ℕ) :
    TaoFivePrimes.arithmeticRestrictLE U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log
      - TaoFivePrimes.arithmeticRestrictLE U (μ : ArithmeticFunction ℝ) *
          TaoFivePrimes.arithmeticRestrictLE V ArithmeticFunction.vonMangoldt *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
      + TaoFivePrimes.arithmeticRestrictGT U (μ : ArithmeticFunction ℝ) *
          TaoFivePrimes.arithmeticRestrictGT V ArithmeticFunction.vonMangoldt *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
      + TaoFivePrimes.arithmeticRestrictLE V ArithmeticFunction.vonMangoldt
      = ArithmeticFunction.vonMangoldt :=
  TaoFivePrimes.vaughan_identity_interface U V
