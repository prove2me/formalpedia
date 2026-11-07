-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammerInf_X_mul_qPochhammerInf_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:55:17.724724+00:00
-- url     : https://prove2.me/submissions/85393601-2c6f-4153-93f6-06ff72ab3b51

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FiniteBinomial
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammerInf_X_mul_qPochhammerInv
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_euler_second_identity
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_Nat_choose_two_succ
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
omit [DiscreteTopology R] in
/-- A family `m ↦ X ^ e m * g m` in `R⟦X⟧` is summable as soon as the exponents `e m`
eventually exceed every fixed degree: only finitely many terms contribute to each
coefficient. -/
private theorem summable_X_pow_mul {e : ℕ → ℕ}
    (he : ∀ d : ℕ, ∃ N : ℕ, ∀ m ≥ N, d < e m) (g : ℕ → R⟦X⟧) :
    Summable fun m : ℕ => (X : R⟦X⟧) ^ e m * g m := by
  refine (PowerSeries.WithPiTopology.summable_iff_summable_coeff R).mpr fun d => ?_
  obtain ⟨N, hN⟩ := he d
  refine summable_of_ne_finset_zero (s := Finset.range N) fun m hm => ?_
  rw [Finset.mem_range, not_lt] at hm
  rw [PowerSeries.coeff_X_pow_mul', if_neg (by have := hN m hm; omega)]
private theorem exists_forall_lt_choose_two (d : ℕ) :
    ∃ N : ℕ, ∀ m ≥ N, d < m.choose 2 := by
  refine ⟨d + 2, fun m hm => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [Nat.choose_two_succ]
  omega
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
    qPochhammerInf (X : R⟦X⟧) * qPochhammerInf (-a) =
    ∑' n : ℕ, X ^ n.choose 2 * a ^ n * qPochhammerInf (X * X ^ n) := by
  have hs : Summable fun n : ℕ => X ^ n.choose 2 * a ^ n * qPochhammerInv (R := R) n := by
    simpa [mul_assoc] using summable_X_pow_mul (R := R)
      exists_forall_lt_choose_two fun n => a ^ n * qPochhammerInv n
  rw [euler_second_identity a, ← Summable.tsum_mul_left _ hs]
  exact tsum_congr fun n => by rw [← qPochhammerInf_X_mul_qPochhammerInv n]; ring
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
