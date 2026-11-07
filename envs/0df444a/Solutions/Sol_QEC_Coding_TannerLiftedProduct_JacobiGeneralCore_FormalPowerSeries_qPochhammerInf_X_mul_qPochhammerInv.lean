-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammerInf_X_mul_qPochhammerInv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:52:41.996675+00:00
-- url     : https://prove2.me/submissions/0a759ec0-0108-4082-8a22-cd30354c467e

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FiniteBinomial
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammerInf_X_eq_qPochhammer_mul


set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
theorem _root_.solution (n : ℕ) :
    qPochhammerInf (X : R⟦X⟧) * qPochhammerInv (R := R) n = qPochhammerInf (X * X ^ n) := by
  rw [qPochhammerInf_X_eq_qPochhammer_mul n, mul_right_comm, qPochhammer_X_mul_qPochhammerInv,
    one_mul]
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
