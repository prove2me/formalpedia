-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.coeff_keySum_eq_coeff_qPochhammerInfInv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:54:32.841355+00:00
-- url     : https://prove2.me/submissions/5381a548-f1b1-4f4f-ac67-e1ed81fd2b2c

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FiniteBinomial
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_summable_keySummand
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_coeff_qPochhammerInv_eq_coeff_qPochhammerInfInv
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
private theorem coeff_tsum {f : ℕ → R⟦X⟧} (hf : Summable f) (d : ℕ) :
    PowerSeries.coeff d (∑' m, f m) = ∑' m, PowerSeries.coeff d (f m) :=
  ((hf.hasSum.map (PowerSeries.coeff d).toAddMonoidHom
    (WithPiTopology.continuous_coeff R d)).tsum_eq).symm
omit [TopologicalSpace R] [DiscreteTopology R] in
/-- `qPochhammerInv 0 = 1`. -/
private theorem qPochhammerInv_zero : qPochhammerInv (R := R) 0 = 1 := by
  simpa using qPochhammer_X_mul_qPochhammerInv (R := R) 0
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
theorem _root_.solution (k : ℕ) (d : ℕ) (hkd : d < k) :
    PowerSeries.coeff d (keySum (R := R) k) = PowerSeries.coeff d (qPochhammerInfInv (R := R)) := by
  rw [keySum, coeff_tsum (summable_keySummand k), tsum_eq_single 0 fun m hm => by
    rw [mul_assoc, PowerSeries.coeff_X_pow_mul',
      if_neg (by have := Nat.pos_of_ne_zero hm; nlinarith)]]
  simpa [qPochhammerInv_zero] using coeff_qPochhammerInv_eq_coeff_qPochhammerInfInv (R := R) hkd
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
