-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsB_psi_evEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:40:48.706829+00:00
-- url     : https://prove2.me/submissions/4304c5b7-c4ad-469a-b002-6fac3f6f9666

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsB_psi_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_isOpen_Mset


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
theorem _root_.solution (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) {x : Y} (hx : x ∈ A.Mset w0 s De) {i : ι}
    (hi : x ∈ (A.chart i).source) : bsPsi A w0 s mu0 σ =ᶠ[𝓝 x] bsPsiC A w0 s mu0 σ i := by
  filter_upwards [(isOpen_Mset A hD).mem_nhds hx, (A.chart i).open_source.mem_nhds hi]
    with y h1 h2
  exact bsB_psi_chart A hD hF hσ h1 h2
end ReciprocityTheory.L2DbarEstimates.Y
