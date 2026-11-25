-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsB_det_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:58:32.590461+00:00
-- url     : https://prove2.me/submissions/d1d6e196-1a6d-4477-8253-9229f8feb89a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsB_jz_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_differentiableAt_det_jz


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
theorem _root_.solution (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) {x : Y}
    (hx : x ∈ A.Mset w0 s De) {i : ι} (hi : x ∈ (A.chart i).source) :
    ∀ᶠ v in 𝓝 (A.chart i x),
      DifferentiableAt ℂ ((fun y => (jz A w0 s i y).det) ∘ (A.chart i).symm) v := by
  filter_upwards [differentiableAt_det_jz A hD hF x hx i hi,
    (A.chart i).open_target.mem_nhds ((A.chart i).map_source hi)] with v h1 h2
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [(A.chart i).open_target.mem_nhds h2] with v' hv'
  simp [bsB_jz_eq A hv']
end ReciprocityTheory.L2DbarEstimates.Y
