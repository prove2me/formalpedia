-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.coeff_qPochhammerInv_eq_coeff_qPochhammerInfInv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:53:43.7002+00:00
-- url     : https://prove2.me/submissions/242a4000-3d93-4b34-aced-092c69fe1713

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FiniteBinomial
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammerInf_X_mul_qPochhammerInv
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_coeff_qPochhammerInf
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_zero
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
end Euler2
section KeyIdentity
private theorem coeff_qPochhammerInf_X_mul_pow {k j : ℕ} (hj : j < k + 1) :
    PowerSeries.coeff j (qPochhammerInf ((X : R⟦X⟧) * X ^ k)) = PowerSeries.coeff j 1 := by
  obtain ⟨g, hg⟩ := exists_qPochhammer_eq_one_add_mul ((X : R⟦X⟧) * X ^ k) (j + 1)
  rw [coeff_qPochhammerInf, hg, map_add, ← pow_succ', PowerSeries.coeff_X_pow_mul',
    if_neg hj.not_ge, add_zero]
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
theorem _root_.solution {k d : ℕ} (hkd : d < k) :
    PowerSeries.coeff d (qPochhammerInv (R := R) k) =
      PowerSeries.coeff d (qPochhammerInfInv (R := R)) := by
  have hQ : ∀ j < k, PowerSeries.coeff j (qPochhammerInf (X : R⟦X⟧) *
      (qPochhammerInv (R := R) k - qPochhammerInfInv (R := R))) = 0 := fun j hj => by
    rw [mul_sub, qPochhammerInf_X_mul_qPochhammerInv, qPochhammerInf_X_mul_qPochhammerInfInv,
      map_sub, sub_eq_zero, coeff_qPochhammerInf_X_mul_pow (by omega)]
  rw [← sub_eq_zero, ← map_sub, show qPochhammerInv (R := R) k - qPochhammerInfInv (R := R) =
    qPochhammerInfInv (R := R) * (qPochhammerInf (X : R⟦X⟧) *
      (qPochhammerInv (R := R) k - qPochhammerInfInv)) from by
        rw [← mul_assoc, qPochhammerInfInv_mul_qPochhammerInf_X, one_mul], PowerSeries.coeff_mul]
  exact Finset.sum_eq_zero fun p hp => by
    rw [hQ p.2 (by have := Finset.mem_antidiagonal.mp hp; omega), mul_zero]
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
