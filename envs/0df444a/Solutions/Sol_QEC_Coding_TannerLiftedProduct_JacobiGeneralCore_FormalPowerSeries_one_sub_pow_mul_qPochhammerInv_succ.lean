-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.one_sub_pow_mul_qPochhammerInv_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:53:37.722461+00:00
-- url     : https://prove2.me/submissions/ef0844fd-53ca-4183-8ae3-dc51acb6e7f5

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FiniteBinomial
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_isUnit_qPochhammer_X
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qPochhammer_succ


set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
omit [TopologicalSpace R] [DiscreteTopology R]
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
theorem _root_.solution (k : ℕ) :
    (1 - (X : R⟦X⟧) ^ (k + 1)) * qPochhammerInv (R := R) (k + 1) = qPochhammerInv k := by
  have h1 := qPochhammer_X_mul_qPochhammerInv (R := R) (k + 1)
  rw [qPochhammer_succ, ← pow_succ'] at h1
  refine (isUnit_qPochhammer_X (R := R) k).mul_left_cancel ?_
  rw [qPochhammer_X_mul_qPochhammerInv, ← mul_assoc, h1]
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
