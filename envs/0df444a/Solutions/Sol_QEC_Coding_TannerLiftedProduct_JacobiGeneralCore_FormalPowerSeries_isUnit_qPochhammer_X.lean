-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.isUnit_qPochhammer_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:34:44.133318+00:00
-- url     : https://prove2.me/submissions/83763fd3-5a6c-44b9-b590-264e8a1d64b8

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPS
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_constantCoeff_qPochhammer_X

set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
omit [TopologicalSpace R] [DiscreteTopology R]
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
theorem _root_.solution (n : ℕ) : IsUnit (qPochhammer (X : R⟦X⟧) n) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_qPochhammer_X]
  exact isUnit_one
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
