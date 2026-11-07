-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.coeff_qBinom_eq_coeff_qPochhammerInv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:53:38.5962+00:00
-- url     : https://prove2.me/submissions/e2c1242a-8154-4e8c-b1db-df7923853266

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FiniteBinomial
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_isUnit_qPochhammer_X
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_mul_qPochhammer_mul_qPochhammer
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_succ_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_right
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qPochhammer_succ
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
omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Every finite q-Pochhammer product is `1` plus a multiple of its argument:
`(a; X)_k = 1 + a * g` for some `g`. -/
private theorem exists_qPochhammer_eq_one_add_mul (a : R⟦X⟧) (k : ℕ) :
    ∃ g : R⟦X⟧, qPochhammer a k = 1 + a * g := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨g, hg⟩ := ih
    exact ⟨g - X ^ k - a * g * X ^ k, by rw [qPochhammer_succ, hg]; ring⟩
omit [TopologicalSpace R] [DiscreteTopology R] in
/-- For `j ≤ m` the `j`-th coefficient of `(X·X^m; X)_k` agrees with that of `1`. -/
private theorem coeff_qPochhammer_X_mul_pow (m k : ℕ) {j : ℕ} (hj : j < m + 1) :
    PowerSeries.coeff j (qPochhammer ((X : R⟦X⟧) * X ^ m) k) = PowerSeries.coeff j 1 := by
  obtain ⟨g, hg⟩ := exists_qPochhammer_eq_one_add_mul ((X : R⟦X⟧) * X ^ m) k
  rw [hg, map_add, ← pow_succ', PowerSeries.coeff_X_pow_mul', if_neg hj.not_ge, add_zero]
omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Telescoping split `(X; X)_n = (X; X)_{n-k} · (X·X^{n-k}; X)_k` for `k ≤ n`. -/
private theorem qPochhammer_X_eq_qPochhammer_mul {k n : ℕ} (hkn : k ≤ n) :
    qPochhammer (X : R⟦X⟧) n =
      qPochhammer (X : R⟦X⟧) (n - k) * qPochhammer ((X : R⟦X⟧) * X ^ (n - k)) k := by
  conv_lhs => rw [show n = n - k + k from (Nat.sub_add_cancel hkn).symm]
  rw [qPochhammer, qPochhammer, qPochhammer, Finset.prod_range_add]
  exact congrArg _ (Finset.prod_congr rfl fun i _ => by ring)
end Euler2
section KeyIdentity
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
omit [TopologicalSpace R] [DiscreteTopology R]
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
theorem _root_.solution {k j n : ℕ} (hjk : j + k ≤ n) :
    PowerSeries.coeff j (QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom n k (X : R⟦X⟧)) =
    PowerSeries.coeff j (qPochhammerInv (R := R) k) := by
  have hkn : k ≤ n := by omega
  have h_eq : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom n k (X : R⟦X⟧) * qPochhammer (X : R⟦X⟧) k *
      qPochhammer (X : R⟦X⟧) (n - k) = qPochhammer (X : R⟦X⟧) n :=
    QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_mul_qPochhammer_mul_qPochhammer (X : R⟦X⟧) hkn
  have hcancel : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom n k (X : R⟦X⟧) * qPochhammer (X : R⟦X⟧) k
      = qPochhammer ((X : R⟦X⟧) * X ^ (n - k)) k := by
    refine (isUnit_qPochhammer_X (R := R) (n - k)).mul_right_cancel ?_
    rw [h_eq, qPochhammer_X_eq_qPochhammer_mul hkn]
    exact mul_comm _ _
  have hdvd : (X : R⟦X⟧) ^ (n - k + 1) ∣
      QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom n k (X : R⟦X⟧) - qPochhammerInv (R := R) k := by
    refine (IsUnit.dvd_mul_right (isUnit_qPochhammer_X (R := R) k)).mp ?_
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [sub_mul, hcancel, qPochhammerInv_mul_qPochhammer_X, map_sub,
      coeff_qPochhammer_X_mul_pow _ _ hm, sub_self]
  rw [← sub_eq_zero, ← map_sub]
  exact PowerSeries.X_pow_dvd_iff.mp hdvd j (by omega)
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
