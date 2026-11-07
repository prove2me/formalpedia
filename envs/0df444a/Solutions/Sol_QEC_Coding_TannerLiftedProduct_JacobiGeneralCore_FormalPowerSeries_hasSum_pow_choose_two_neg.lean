-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.hasSum_pow_choose_two_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:56:44.455518+00:00
-- url     : https://prove2.me/submissions/1a038d15-51e5-42a1-a81e-2cac30e55799

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FiniteBinomial
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammerInf_X_mul_qPochhammerInv
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_summable_keySummand
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_keySum_eq_qPochhammerInfInv
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_Nat_choose_two_add_choose_two__59bcef2a28c6

section
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
section Euler2
end Euler2
section KeyIdentity
end KeyIdentity
section Cauchy
private theorem hasSum_pow_mul_qPochhammerInf_mul_qPochhammerInv (k e : ℕ) :
    HasSum (fun m : ℕ => X ^ (e + m * (m + k)) * qPochhammerInf (X : R⟦X⟧) *
      qPochhammerInv (R := R) m * qPochhammerInv (m + k)) (X ^ e : R⟦X⟧) := by
  have h : HasSum (fun m : ℕ =>
      X ^ (m * (m + k)) * qPochhammerInv (R := R) m * qPochhammerInv (m + k))
      (qPochhammerInfInv (R := R)) := by
    rw [← keySum_eq_qPochhammerInfInv (R := R) k]
    exact (summable_keySummand k).hasSum
  have key := h.mul_left ((X : R⟦X⟧) ^ e * qPochhammerInf X)
  rw [mul_assoc, qPochhammerInf_X_mul_qPochhammerInfInv, mul_one] at key
  have hfun : (fun m : ℕ => (X : R⟦X⟧) ^ e * qPochhammerInf X *
      (X ^ (m * (m + k)) * qPochhammerInv (R := R) m * qPochhammerInv (m + k))) =
      fun m : ℕ => X ^ (e + m * (m + k)) * qPochhammerInf (X : R⟦X⟧) *
        qPochhammerInv (R := R) m * qPochhammerInv (m + k) := by
    funext m; rw [pow_add]; ring
  exact hfun ▸ key
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
theorem _root_.solution (l : ℕ) :
    HasSum (fun n : ℕ =>
      X ^ n.choose 2 * qPochhammerInf (X * X ^ n) *
      (X ^ (n + (l + 1)).choose 2 * X ^ (n + (l + 1)) * qPochhammerInv (R := R) (n + (l + 1))))
      (X ^ (l + 2).choose 2 : R⟦X⟧) := by
  convert hasSum_pow_mul_qPochhammerInf_mul_qPochhammerInv (R := R) (l + 1)
    ((l + 2).choose 2) using 1
  funext n
  rw [← qPochhammerInf_X_mul_qPochhammerInv n, ← Nat.choose_two_add_choose_two' n l]
  ring
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
