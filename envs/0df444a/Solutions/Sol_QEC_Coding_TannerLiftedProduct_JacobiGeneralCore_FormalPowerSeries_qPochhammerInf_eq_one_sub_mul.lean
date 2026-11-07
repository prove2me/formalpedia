-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammerInf_eq_one_sub_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:47:01.065445+00:00
-- url     : https://prove2.me/submissions/b0375b1c-3dff-4de3-9994-b84ff9c82279

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.PiTopology
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPS
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_multipliable_one_sub_mul_pow

set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
theorem _root_.solution (a : R⟦X⟧) :
    qPochhammerInf a = (1 - a) * qPochhammerInf (a * X) := by
  -- The shifted partial products converge to `(aX; X)_∞`.
  have h_shift : Filter.Tendsto (fun n => ∏ k ∈ range n, (1 - a * X ^ (k + 1))) Filter.atTop
      (nhds (qPochhammerInf (a * X))) :=
    (multipliable_one_sub_mul_pow (a * X)).hasProd.tendsto_prod_nat.congr
      fun n => prod_congr rfl fun k _ => by ring
  -- The partial products of `(a; X)_∞`, reindexed, converge to `(a; X)_∞`.
  have h_all : Filter.Tendsto (fun n => ∏ k ∈ range (n + 1), (1 - a * X ^ k)) Filter.atTop
      (nhds (qPochhammerInf a)) :=
    (multipliable_one_sub_mul_pow a).hasProd.tendsto_prod_nat.comp (Filter.tendsto_add_atTop_nat 1)
  refine tendsto_nhds_unique h_all ?_
  have hsplit : ∀ n : ℕ, ∏ k ∈ range (n + 1), (1 - a * X ^ k)
      = (1 - a) * ∏ k ∈ range n, (1 - a * X ^ (k + 1)) := fun n => by
    rw [prod_range_succ', pow_zero, mul_one, mul_comm]
  simp_rw [hsplit]
  exact tendsto_const_nhds.mul h_shift
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
