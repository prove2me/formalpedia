-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.constantCoeff_qPochhammer_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:33:55.487617+00:00
-- url     : https://prove2.me/submissions/07433efd-ffdd-4d8e-a70a-bd2058d58fd8

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPS
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammer_zero



set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
omit [TopologicalSpace R] [DiscreteTopology R]
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
theorem _root_.solution (n : ℕ) :
    constantCoeff (qPochhammer (X : R⟦X⟧) n) = 1 := by
  induction n with
  | zero => simp [qPochhammer]
  | succ n ih =>
    rw [qPochhammer_succ]
    simp [map_mul, map_sub, ih]
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
