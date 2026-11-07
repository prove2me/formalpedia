-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.keySum_sub_keySum_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:54:16.279895+00:00
-- url     : https://prove2.me/submissions/03aba424-674d-4fb0-ac81-7a9bffcc4dc0

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FiniteBinomial
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_one_sub_pow_mul_qPochhammerInv_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_summable_keySummand
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_succ_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_right
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_succ_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_right
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_succ
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qPochhammer_zero


section
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
section Euler2
end Euler2
section KeyIdentity
omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Key auxiliary: `qPochhammerInv(n-1) + X^n * qPochhammerInv(n) = qPochhammerInv(n)`.
    Equivalently,
    `(1 - X^{n+1}) * qPochhammerInv(n+1) + X^{n+1} * qPochhammerInv(n+1) = qPochhammerInv(n+1)`. -/
private theorem qPochhammerInv_add_pow_mul_qPochhammerInv_succ (n : ℕ) :
    qPochhammerInv (R := R) n + X ^ (n + 1) * qPochhammerInv (R := R) (n + 1) =
    qPochhammerInv (R := R) (n + 1) := by
  rw [← one_sub_pow_mul_qPochhammerInv_succ (R := R) n]; ring
private theorem keySumShift_eq_keySum_add (k : ℕ) :
    keySumShift (R := R) k = keySum k + X ^ (k + 1) * keySum (k + 1) := by
  unfold keySumShift keySum
  rw [← Summable.tsum_mul_left _ (summable_keySummand (R := R) (k + 1)),
    ← Summable.tsum_add (summable_keySummand (R := R) k)
      (Summable.mul_left _ (summable_keySummand (R := R) (k + 1)))]
  refine tsum_congr fun m => ?_
  simp only [← add_assoc]
  have hpow : (X : R⟦X⟧) ^ (k + 1) * X ^ (m * (m + k + 1)) =
      X ^ (m + k + 1) * X ^ (m * (m + k)) := by
    rw [← pow_add, ← pow_add]; congr 1; ring
  rw [← one_sub_pow_mul_qPochhammerInv_succ (R := R) (m + k), ← mul_assoc ((X : R⟦X⟧) ^ (k + 1)),
    ← mul_assoc ((X : R⟦X⟧) ^ (k + 1)), hpow]
  generalize (X : R⟦X⟧) ^ (m * (m + k)) = A
  ring
private theorem hasSum_pow_mul_keySum (k : ℕ) :
    HasSum (fun n : ℕ =>
      X ^ ((n + 1) * (n + 1 + k)) * qPochhammerInv (R := R) n * qPochhammerInv (n + k + 2))
      (X ^ (k + 1) * keySum (R := R) (k + 2)) := by
  have hfun : (fun n : ℕ => (X : R⟦X⟧) ^ (k + 1) *
      (X ^ (n * (n + (k + 2))) * qPochhammerInv (R := R) n * qPochhammerInv (n + (k + 2)))) =
      fun n : ℕ => X ^ ((n + 1) * (n + 1 + k)) * qPochhammerInv (R := R) n *
        qPochhammerInv (n + k + 2) := by
    funext n
    rw [show n + (k + 2) = n + k + 2 from by omega,
      show (n + 1) * (n + 1 + k) = k + 1 + n * (n + k + 2) from by ring, pow_add]
    ring
  exact hfun ▸ (summable_keySummand (R := R) (k + 2)).hasSum.mul_left _
private theorem keySumShift_eq_keySum_succ_add (k : ℕ) :
    keySumShift (R := R) k = keySum (k + 1) + X ^ (k + 1) * keySum (k + 2) := by
  have hA := (hasSum_nat_add_iff' (f := fun m : ℕ =>
    X ^ (m * (m + (k + 1))) * qPochhammerInv (R := R) m * qPochhammerInv (m + (k + 1))) 1).mpr
      (summable_keySummand (R := R) (k + 1)).hasSum
  refine HasSum.tsum_eq ((hasSum_nat_add_iff' 1).mp ?_)
  convert hA.add (hasSum_pow_mul_keySum (R := R) k) using 1
  · funext n
    rw [show n + 1 + k + 1 = n + k + 2 from by omega,
      show n + 1 + (k + 1) = n + k + 2 from by omega,
      show (n + 1) * (n + k + 2) = (n + 1) * (n + 1 + k) + (n + 1) from by ring, pow_add]
    conv_lhs => rw [← qPochhammerInv_add_pow_mul_qPochhammerInv_succ (R := R) n]
    ring
  · simp only [keySum, Finset.sum_range_one, Nat.zero_mul, Nat.zero_add, pow_zero, one_mul]
    ring
end KeyIdentity
section Cauchy
end Cauchy
section JTP
end JTP
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
end
end

set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
theorem _root_.solution (k : ℕ) :
    keySum (R := R) k - keySum (k + 1) =
    X ^ (k + 1) * (keySum (R := R) (k + 2) - keySum (k + 1)) := by
  have h := (keySumShift_eq_keySum_add (R := R) k).symm.trans (keySumShift_eq_keySum_succ_add k)
  rw [mul_sub, sub_eq_sub_iff_add_eq_add]
  exact h.trans (add_comm _ _)
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
