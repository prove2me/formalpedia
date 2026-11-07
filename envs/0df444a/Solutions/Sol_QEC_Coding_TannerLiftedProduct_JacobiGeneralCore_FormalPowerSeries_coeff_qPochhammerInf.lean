-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.coeff_qPochhammerInf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:48:04.05922+00:00
-- url     : https://prove2.me/submissions/f4532f80-2583-4612-bd15-dd62e7ea778d

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.PiTopology
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPS
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_coeff_qPochhammer_eq_of_le
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_multipliable_one_sub_mul_pow

set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
theorem _root_.solution (a : R⟦X⟧) (d : ℕ) :
    coeff d (qPochhammerInf a) = coeff d (qPochhammer a (d + 1)) := by
  have h_limit : Filter.Tendsto (fun n => coeff d (qPochhammer a n)) Filter.atTop
      (nhds (coeff d (qPochhammerInf a))) :=
    ((WithPiTopology.continuous_coeff R d).tendsto _).comp
      (multipliable_one_sub_mul_pow a).hasProd.tendsto_prod_nat
  refine tendsto_nhds_unique h_limit (tendsto_const_nhds.congr' ?_)
  filter_upwards [Filter.eventually_ge_atTop (d + 1)] with n hn
  exact (coeff_qPochhammer_eq_of_le a (Nat.lt_succ_self _) hn).symm
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
