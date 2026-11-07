-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_mul_qPochhammer_mul_qPochhammer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:47:31.772107+00:00
-- url     : https://prove2.me/submissions/7c019ead-e932-4426-ae73-715de371275e

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Defs.Filter
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_Defs
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qPochhammer_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_succ_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_right
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_succ_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_eq_zero_of_lt
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_self
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_succ
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_succ_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_right

set_option autoImplicit false
open Finset Filter
open scoped Topology
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore
variable {R : Type*}
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore
theorem _root_.solution [CommRing R] (q : R) :
    ∀ {n k : ℕ}, k ≤ n →
      qBinom n k q * qPochhammer q q k * qPochhammer q q (n - k)
        = qPochhammer q q n := by
  intro n
  induction n with
  | zero =>
    rintro k hk
    obtain rfl : k = 0 := by omega
    simp
  | succ n ih =>
    rintro (_ | k) hk
    · simp
    obtain hlt | rfl : k + 1 ≤ n ∨ n = k := by omega
    · -- Interior case: write `n = k + 1 + m` and feed in both induction hypotheses.
      obtain ⟨m, rfl⟩ : ∃ m, n = k + 1 + m := ⟨n - (k + 1), by omega⟩
      have ih1 := ih (show k + 1 ≤ k + 1 + m by omega)
      have ih2 := ih (show k ≤ k + 1 + m by omega)
      rw [show k + 1 + m - (k + 1) = m from by omega, qPochhammer_succ q q k] at ih1
      rw [show k + 1 + m - k = m + 1 from by omega, qPochhammer_succ q q m] at ih2
      rw [qBinom_succ_succ, show k + 1 + m + 1 - (k + 1) = m + 1 from by omega,
        show k + 1 + m - k = m + 1 from by omega, qPochhammer_succ q q k,
        qPochhammer_succ q q m, qPochhammer_succ q q (k + 1 + m)]
      linear_combination (1 - q * q ^ m) * ih1 + q ^ (m + 1) * (1 - q * q ^ k) * ih2
    · -- Diagonal case `k = n`.
      rw [qBinom_succ_succ, qBinom_eq_zero_of_lt q (Nat.lt_succ_self _), qBinom_self,
        Nat.sub_self, Nat.sub_self, pow_zero, qPochhammer_zero]
      ring
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore
