-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.prod_one_add_mul_pow_eq_sum_qBinom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:47:08.470773+00:00
-- url     : https://prove2.me/submissions/101d1161-8989-4e6e-a9c5-e785c64c2554

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FiniteBinomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_Nat_choose_two_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_eq_zero_of_lt
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_succ_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_succ_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_right
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_succ_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_right
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_succ
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qPochhammer_zero



set_option autoImplicit false
open Finset Filter
open scoped Topology
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore
variable {R : Type*}
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore
theorem _root_.solution [CommRing R] (q z : R) (n : ℕ) :
    ∏ k ∈ Finset.range n, (1 + z * q ^ k)
      = ∑ k ∈ Finset.range (n + 1), q ^ k.choose 2 * qBinom n k q * z ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      rw [Finset.sum_range_succ'
            (fun k => q ^ k.choose 2 * qBinom (n + 1) k q * z ^ k) (n + 1)]
      simp only [Nat.choose_zero_succ, pow_zero, qBinom_succ_zero, mul_one]
      have stepB :
          (∑ k ∈ Finset.range (n + 1),
              q ^ (k + 1).choose 2 * qBinom (n + 1) (k + 1) q * z ^ (k + 1))
            = (∑ k ∈ Finset.range (n + 1),
                  q ^ (k + 1).choose 2 * qBinom n (k + 1) q * z ^ (k + 1))
              + ∑ k ∈ Finset.range (n + 1),
                  q ^ (k + 1).choose 2 * q ^ (n - k) * qBinom n k q
                    * z ^ (k + 1) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [qBinom_succ_succ]
        ring
      rw [stepB]
      have stepC :
          (∑ k ∈ Finset.range (n + 1),
              q ^ (k + 1).choose 2 * q ^ (n - k) * qBinom n k q * z ^ (k + 1))
            = z * q ^ n *
                ∑ k ∈ Finset.range (n + 1),
                    q ^ k.choose 2 * qBinom n k q * z ^ k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        have hkle : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [Nat.choose_two_succ k, pow_add q (k.choose 2) k,
            mul_assoc (q ^ k.choose 2) (q ^ k) (q ^ (n - k)),
            ← pow_add q k (n - k),
            show k + (n - k) = n from by omega,
            pow_succ z k]
        ring
      rw [stepC]
      have stepD :
          (∑ k ∈ Finset.range (n + 1), q ^ k.choose 2 * qBinom n k q * z ^ k)
            = (∑ k ∈ Finset.range (n + 1),
                  q ^ (k + 1).choose 2 * qBinom n (k + 1) q * z ^ (k + 1)) + 1 := by
        have h := Finset.sum_range_succ'
          (fun k => q ^ k.choose 2 * qBinom n k q * z ^ k) (n + 1)
        simp only [Nat.choose_zero_succ, pow_zero, qBinom_zero_right, mul_one] at h
        rw [Finset.sum_range_succ
              (f := fun k => q ^ k.choose 2 * qBinom n k q * z ^ k) (n := n + 1),
            qBinom_eq_zero_of_lt q (Nat.lt_succ_self n)] at h
        simp only [mul_zero, zero_mul, add_zero] at h
        exact h
      linear_combination stepD
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore
