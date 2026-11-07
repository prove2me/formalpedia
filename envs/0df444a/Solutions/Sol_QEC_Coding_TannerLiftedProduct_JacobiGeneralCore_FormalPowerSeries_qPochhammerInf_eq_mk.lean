-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammerInf_eq_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:42:23.320146+00:00
-- url     : https://prove2.me/submissions/b2fcf328-e596-4d67-8bd6-a5c50c3d5d05

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.PiTopology
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPS
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_coeff_qPochhammerInf
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammer_zero

set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
theorem _root_.solution (a : R⟦X⟧) :
    qPochhammerInf a = mk fun d => coeff d (qPochhammer a (d + 1)) := by
  ext d; rw [coeff_mk, coeff_qPochhammerInf]
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
