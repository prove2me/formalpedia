-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsB_jz_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:28:22.453876+00:00
-- url     : https://prove2.me/submissions/d6236eb3-3fa7-41cf-b57c-0d642eec4d4a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepB

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
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}
variable {mu0 : La} {σ : ι → Y → ℂ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {i : ι} {v : V n} (hv : v ∈ (A.chart i).target) :
    jz A w0 s i ((A.chart i).symm v) = fderiv ℂ (A.zLoc w0 s i) v := by
  unfold jz; rw [(A.chart i).right_inv hv]
end ReciprocityTheory.L2DbarEstimates.Y
