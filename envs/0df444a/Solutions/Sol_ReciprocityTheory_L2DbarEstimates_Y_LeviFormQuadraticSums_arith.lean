-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums.arith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:30:53.212784+00:00
-- url     : https://prove2.me/submissions/7a6cac16-f269-41d6-9f22-64ad0e78d358

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeDA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeD
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums
variable {n d : ℕ} {p : V n → V d} {U : Set (V n)}
namespace ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums
theorem _root_.solution {a b t L s : ℝ} (ha : 0 ≤ a) (hab : 0 ≤ a + t * b) (hL : 0 ≤ L) (hs0 : 0 ≤ s)
    (hs : s ≤ t * L) : 0 ≤ a * L + b * s := by
  rcases le_total 0 b with hb | hb
  · positivity
  · nlinarith [mul_le_mul_of_nonpos_left hs hb, mul_nonneg hab hL]
end ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums
