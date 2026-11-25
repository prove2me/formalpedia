-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fc_mem_O
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:43:47.287604+00:00
-- url     : https://prove2.me/submissions/34a05efa-5432-4173-ae1b-8c8c5adaef47

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcB

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
theorem _root_.solution {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (x : A.Mset w0 s De) (i : ι)
    (hxi : (x : Y) ∈ (A.chart i).source) :
    A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De := by
  refine ⟨(A.chart i).map_source hxi, ?_⟩
  show (A.chart i).symm (A.chart i x) ∈ A.Mset w0 s De
  rw [(A.chart i).left_inv hxi]
  exact x.2
end ReciprocityTheory.L2DbarEstimates.Y
