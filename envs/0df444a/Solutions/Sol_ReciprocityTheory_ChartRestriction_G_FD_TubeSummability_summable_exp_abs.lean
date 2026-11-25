-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.TubeSummability.summable_exp_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:00:07.829065+00:00
-- url     : https://prove2.me/submissions/36639798-ee21-4b48-a533-066e3c7b0f7c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourIndep
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TubeSummability

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TubeSummability
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
  ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity ReciprocityTheory.L2DbarEstimates.Y
open scoped ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.G.FD.TubeSummability
theorem _root_.solution (c : ℝ) (hc : 0 < c) :
    ∀ n : ℕ, Summable (fun k : Fin n → ℤ => Real.exp (-c * ∑ j, |(k j : ℝ)|)) := by
  have hgeo : Summable (fun m : ℕ => Real.exp (-c) ^ m) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (by simpa using Real.exp_lt_exp.2 (by linarith : -c < 0))
  have h1 : Summable (fun m : ℤ => Real.exp (-c * |(m : ℝ)|)) := by
    apply Summable.of_nat_of_neg
    · refine hgeo.congr fun m => ?_
      simp only [Function.comp, Int.cast_natCast, Nat.abs_cast]
      rw [← Real.exp_nat_mul]
      ring_nf
    · refine hgeo.congr fun m => ?_
      simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast]
      rw [← Real.exp_nat_mul]
      ring_nf
  intro n
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℤ).summable_iff]
    convert h1.mul_of_nonneg ih (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le) using 1
    funext p
    simp [Fin.consEquiv, Fin.sum_univ_succ, mul_add, Real.exp_add]
end ReciprocityTheory.ChartRestriction.G.FD.TubeSummability
