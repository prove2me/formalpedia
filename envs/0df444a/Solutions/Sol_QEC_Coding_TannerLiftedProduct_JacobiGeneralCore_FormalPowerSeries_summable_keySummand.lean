-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.summable_keySummand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:52:42.949039+00:00
-- url     : https://prove2.me/submissions/939c0480-3111-4e0b-941c-c130f4fc0e0e

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FiniteBinomial
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
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
private theorem exists_forall_lt_mul (k d : ℕ) : ∃ N : ℕ, ∀ m ≥ N, d < m * (m + k) :=
  ⟨d + 1, fun m hm => lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right m (by omega))⟩
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
omit [DiscreteTopology R]
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
theorem _root_.solution (k : ℕ) :
    Summable (fun m : ℕ =>
      X ^ (m * (m + k)) * qPochhammerInv (R := R) m * qPochhammerInv (m + k)) := by
  simpa [mul_assoc] using summable_X_pow_mul (R := R)
    (exists_forall_lt_mul k) fun m => qPochhammerInv m * qPochhammerInv (m + k)
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
