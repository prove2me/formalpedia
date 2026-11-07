-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.coeff_qPochhammer_eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:47:21.9492+00:00
-- url     : https://prove2.me/submissions/349a49e3-9c2b-4693-9b9c-728ddf62af53

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.PiTopology
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPS
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_coeff_qPochhammer_succ

set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R]
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
theorem _root_.solution (a : R⟦X⟧) {d M N : ℕ}
    (hM : d < M) (hN : M ≤ N) :
    coeff d (qPochhammer a N) = coeff d (qPochhammer a M) := by
  induction hN with
  | refl => rfl
  | step hN ih =>
      convert coeff_qPochhammer_succ a (lt_of_lt_of_le hM hN) using 1
      exact ih.symm
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
