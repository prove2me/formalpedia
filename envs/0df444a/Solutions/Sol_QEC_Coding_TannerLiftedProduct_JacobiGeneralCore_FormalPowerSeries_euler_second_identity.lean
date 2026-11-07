-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.euler_second_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:54:28.137091+00:00
-- url     : https://prove2.me/submissions/f681331c-cc0c-450a-931f-5c4e624f9992

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FiniteBinomial
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_coeff_qBinom_eq_coeff_qPochhammerInv
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_coeff_qPochhammerInf
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_Nat_le_choose_two_add_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_Nat_lt_choose_two_of_add_two_le
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_prod_one_add_mul_pow_eq_sum_qBinom
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
omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Two power series agreeing in all coefficients below `N` still agree there after
multiplication by a common factor. -/
private theorem coeff_mul_congr {f g b : R⟦X⟧} {N j : ℕ} (hj : j < N)
    (h : ∀ i < N, PowerSeries.coeff i f = PowerSeries.coeff i g) :
    PowerSeries.coeff j (f * b) = PowerSeries.coeff j (g * b) := by
  have hd : (X : R⟦X⟧) ^ N ∣ f - g :=
    PowerSeries.X_pow_dvd_iff.mpr fun i hi => by rw [map_sub, h i hi, sub_self]
  have hj0 := PowerSeries.X_pow_dvd_iff.mp (hd.mul_right b) j hj
  rwa [sub_mul, map_sub, sub_eq_zero] at hj0
omit [TopologicalSpace R] [DiscreteTopology R] in
private theorem qPochhammer_neg_eq_sum (a : R⟦X⟧) (n : ℕ) :
    qPochhammer (-a) n = ∑ k ∈ Finset.range (n + 1),
      X ^ k.choose 2 * QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom n k (X : R⟦X⟧) * a ^ k := by
  rw [qPochhammer, ← QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.prod_one_add_mul_pow_eq_sum_qBinom (X : R⟦X⟧) a n]
  exact Finset.prod_congr rfl fun _ _ => by ring
omit [TopologicalSpace R] [DiscreteTopology R] in
private theorem coeff_eq_zero_of_lt_choose_two (a : R⟦X⟧) (d k : ℕ) (hk : d < k.choose 2) :
    PowerSeries.coeff d (X ^ k.choose 2 * a ^ k * qPochhammerInv (R := R) k) = 0 := by
  rw [mul_assoc, PowerSeries.coeff_X_pow_mul', if_neg hk.not_ge]
omit [DiscreteTopology R] in
/-- The Euler-second summands `X^{C(k,2)} · a^k · (X; X)_k⁻¹` form a summable family. -/
private theorem summable_pow_choose_two_mul_pow_mul_qPochhammerInv (a : R⟦X⟧) :
    Summable fun k : ℕ => (X : R⟦X⟧) ^ k.choose 2 * a ^ k * qPochhammerInv (R := R) k := by
  refine (WithPiTopology.summable_iff_summable_coeff R).mpr fun d => ?_
  refine summable_of_ne_finset_zero (s := Finset.range (d + 2)) fun k hk => ?_
  exact coeff_eq_zero_of_lt_choose_two a d k (Nat.lt_choose_two_of_add_two_le (by simpa using hk))
omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Termwise agreement, in degree `n`, between the finite q-binomial expansion of
`(-a; X)_{n+1}` and the Euler-second summands. -/
private theorem coeff_pow_choose_two_mul_qBinom_mul_pow (a : R⟦X⟧) (n k : ℕ) :
    PowerSeries.coeff n ((X : R⟦X⟧) ^ k.choose 2 * QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom (n + 1) k X * a ^ k) =
      PowerSeries.coeff n ((X : R⟦X⟧) ^ k.choose 2 * a ^ k * qPochhammerInv (R := R) k) := by
  rw [mul_assoc, show (X : R⟦X⟧) ^ k.choose 2 * a ^ k * qPochhammerInv (R := R) k
      = X ^ k.choose 2 * (qPochhammerInv (R := R) k * a ^ k) from by ring,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · refine coeff_mul_congr (N := n - k.choose 2 + 1) (by omega) fun i hi => ?_
    exact coeff_qBinom_eq_coeff_qPochhammerInv (by have := Nat.le_choose_two_add_one k; omega)
  · rfl
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
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
theorem _root_.solution (a : R⟦X⟧) :
    qPochhammerInf (-a) = ∑' k : ℕ, X ^ k.choose 2 * a ^ k * qPochhammerInv (R := R) k := by
  ext n
  have hcoeff :
      ∑' k : ℕ, PowerSeries.coeff n ((X : R⟦X⟧) ^ k.choose 2 * a ^ k * qPochhammerInv (R := R) k)
        = PowerSeries.coeff n
            (∑' k : ℕ, (X : R⟦X⟧) ^ k.choose 2 * a ^ k * qPochhammerInv (R := R) k) :=
    ((summable_pow_choose_two_mul_pow_mul_qPochhammerInv a).hasSum.map
      (PowerSeries.coeff n).toAddMonoidHom (WithPiTopology.continuous_coeff R n)).tsum_eq
  rw [coeff_qPochhammerInf, qPochhammer_neg_eq_sum, ← hcoeff,
    tsum_eq_sum (s := Finset.range (n + 2)) fun k hk =>
      coeff_eq_zero_of_lt_choose_two a n k (Nat.lt_choose_two_of_add_two_le (by simpa using hk)),
    map_sum]
  exact Finset.sum_congr rfl fun k _ => coeff_pow_choose_two_mul_qBinom_mul_pow a n k
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
