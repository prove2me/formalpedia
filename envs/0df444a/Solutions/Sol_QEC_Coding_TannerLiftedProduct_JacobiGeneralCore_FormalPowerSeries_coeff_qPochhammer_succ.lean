-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.coeff_qPochhammer_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:46:42.373136+00:00
-- url     : https://prove2.me/submissions/142c39c4-0a42-4bde-9c35-cc94d91214cf

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.PiTopology
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPS
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_succ

set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R]
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
theorem _root_.solution (a : R⟦X⟧) {d n : ℕ} (hdn : d < n) :
    coeff d (qPochhammer a (n + 1)) = coeff d (qPochhammer a n) := by
  rw [qPochhammer_succ, mul_sub, mul_one, map_sub, ← mul_assoc,
    PowerSeries.coeff_mul_X_pow', if_neg hdn.not_ge, sub_zero]
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
