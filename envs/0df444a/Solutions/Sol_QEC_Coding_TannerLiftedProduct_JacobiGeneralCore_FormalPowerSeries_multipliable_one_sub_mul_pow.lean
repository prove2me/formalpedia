-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.multipliable_one_sub_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:33:22.501945+00:00
-- url     : https://prove2.me/submissions/bf89260f-3397-44f8-8e9a-2735541566fb

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.PiTopology
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPS
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammer_zero

set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
omit [DiscreteTopology R]
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
theorem _root_.solution (a : R⟦X⟧) :
    Multipliable (fun k : ℕ => 1 - a * X ^ k) := by
  have hord : ∀ k : ℕ, (k : ℕ∞) ≤ (-(a * X ^ k) : R⟦X⟧).order := fun k =>
    PowerSeries.le_order _ _ fun i hi => by
      have hik : i < k := by exact_mod_cast hi
      rw [map_neg, PowerSeries.coeff_mul_X_pow', if_neg hik.not_ge, neg_zero]
  simp only [sub_eq_add_neg]
  refine WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top R
    (ENat.tendsto_nhds_top_iff_natCast_lt.2 fun n => Filter.eventually_atTop.2 ⟨n + 1, ?_⟩)
  exact fun k hk => lt_of_lt_of_le (by exact_mod_cast hk) (hord k)
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
