-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fn_sum_le_totalDegree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:46:03.261288+00:00
-- url     : https://prove2.me/submissions/ede45140-bff8-4488-8711-07638c2511fd

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ImportsAlt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Set
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} (De : MvPolynomial (Fin n) ℂ)
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {m : Fin n →₀ ℕ} (hm : m ∈ De.support) :
    ∑ k, m k ≤ De.totalDegree := by
  have h := MvPolynomial.le_totalDegree hm
  first
    | (rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h)
    | (simpa [Finsupp.degree, Finsupp.sum_fintype] using h)
    | (rwa [Finsupp.degree_eq_sum] at h)
end ReciprocityTheory.L2DbarEstimates.Y
