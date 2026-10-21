-- Prove2me | solution 1 for VehicleSharePricing.MultiNet.chu_vandermonde
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:46:29.435306+00:00
-- url     : https://prove2.me/submissions/33569d5b-9949-4c04-963b-b7e805a3ca2f

import Mathlib
import Definitions.Def_VehicleSharePricing_MultiNet_GenBinom

set_option autoImplicit false
open VehicleSharePricing.MultiNet Finset

lemma desc_smeval (n : ℕ) (a : ℝ) :
    (descPochhammer ℤ n).smeval a = ∏ i ∈ Finset.range n, (a - (i : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [descPochhammer_succ_right, Polynomial.smeval_mul, ih, Finset.prod_range_succ]
    simp [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast]

lemma gbinom_eq_choose (x : ℝ) (k : ℕ) : gbinom x k = Ring.choose x k := by
  rw [Ring.choose_eq_smul, desc_smeval, gbinom]
  rw [Algebra.smul_def]
  simp [div_eq_inv_mul]

lemma nop (n : ℕ) (x : ℝ) : Int.negOnePow n • x = (-1 : ℝ) ^ n * x := by
  rw [Int.negOnePow_def, Units.smul_def]
  simp

lemma multichoose_add (r s : ℝ) (k : ℕ) :
    Ring.multichoose (r + s) k = ∑ ij ∈ antidiagonal k, Ring.multichoose r ij.1 * Ring.multichoose s ij.2 := by
  have h := Ring.add_choose_eq (r := -r) (s := -s) k (Commute.all _ _)
  have e : -r + -s = -(r + s) := by ring
  rw [e] at h
  simp_rw [Ring.choose_neg', nop] at h
  have h2 : (-1 : ℝ) ^ k * Ring.multichoose (r + s) k =
      (-1 : ℝ) ^ k * ∑ ij ∈ antidiagonal k, Ring.multichoose r ij.1 * Ring.multichoose s ij.2 := by
    rw [h, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro ij hij
    have hk : ij.1 + ij.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.1 hij
    rw [← hk, pow_add]
    ring
  have : ((-1 : ℝ) ^ k) ≠ 0 := by simp
  exact mul_left_cancel₀ this h2

theorem solution (T₁ T₂ : ℝ) (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (K : ℕ) :
    ∑ K₁ ∈ Finset.range (K + 1),
        gbinom ((K : ℝ) + (T₁ + T₂) - (K₁ : ℝ) - T₁ - 1) (K - K₁) * gbinom (T₁ + (K₁ : ℝ) - 1) K₁ =
      gbinom ((K : ℝ) + (T₁ + T₂) - 1) K := by
  have h := multichoose_add T₁ T₂ K
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  have hR : gbinom ((K : ℝ) + (T₁ + T₂) - 1) K = Ring.multichoose (T₁ + T₂) K := by
    rw [gbinom_eq_choose, Ring.multichoose_eq]; congr 1; ring
  rw [hR, h]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hiK : i ≤ K := by simpa [Nat.lt_succ_iff] using hi
  rw [gbinom_eq_choose, gbinom_eq_choose, Ring.multichoose_eq, Ring.multichoose_eq, mul_comm]
  congr 2
  · push_cast [Nat.cast_sub hiK]; ring
