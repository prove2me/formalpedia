-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsB_psi_smoothAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:50:21.903796+00:00
-- url     : https://prove2.me/submissions/2e6d9a45-144d-4fa5-b06f-75cf75c487c6

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsB_psiC_smooth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsB_psi_evEq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add


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
    (hi : x ∈ (A.chart i).source) :
    ContDiffAt ℝ ∞ (bsPsi A w0 s mu0 σ ∘ (A.chart i).symm) (A.chart i x) := by
  obtain ⟨h1, h2, h3⟩ := bsB_psiC_smooth A hD hF hσ hx hi
  have hC : ContDiffAt ℝ ∞ (bsPsiC A w0 s mu0 σ i ∘ (A.chart i).symm) (A.chart i x) :=
    (h1.add h2).add h3
  refine hC.congr_of_eventuallyEq ?_
  have ht : Tendsto (A.chart i).symm (𝓝 (A.chart i x)) (𝓝 x) := by
    have := (A.chart i).continuousAt_symm ((A.chart i).map_source hi)
    rwa [ContinuousAt, (A.chart i).left_inv hi] at this
  exact (bsB_psi_evEq A hD hF hσ hx hi).comp_tendsto ht
end ReciprocityTheory.L2DbarEstimates.Y
