-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fc_zLoc_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:58:23.195842+00:00
-- url     : https://prove2.me/submissions/636681d3-8cdf-4d28-82b6-c31b76445b8d

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_zLoc_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal
noncomputable section
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s)
    (e : OpenPartialHomeomorph (A.Mset w0 s De) (V n)) (he : IsChart n (fun y : A.Mset w0 s De => A.zmap w0 s y) e)
    (x : A.Mset w0 s De) (hxe : x ∈ e.source) (i : ι) (hxi : (x : Y) ∈ (A.chart i).source) :
    A.zLoc w0 s i (A.chart i x) = e x := by
  rw [fc_zLoc_eq A hD i _ ((A.chart i).map_source hxi), (A.chart i).left_inv hxi]
  exact he hxe
end ReciprocityTheory.L2DbarEstimates.Y
