-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsB_psiC_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:22:48.190089+00:00
-- url     : https://prove2.me/submissions/54b5beff-9e9b-4633-9974-2c2a1be2b6c2

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsB_logsq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsB_O_open
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsB_O_mem
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsB_jz_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsB_inv_diffOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_ne_of_tr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_contDiffAt_det_jz
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_jz_det_ne


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
    ContDiffAt ℝ ∞ (A.ph (mu0 - A.kap) i ∘ (A.chart i).symm) (A.chart i x) ∧
    ContDiffAt ℝ ∞ ((fun y => Real.log (‖(σ i y)⁻¹‖ ^ 2)) ∘ (A.chart i).symm) (A.chart i x) ∧
    ContDiffAt ℝ ∞ ((fun y => Real.log (‖(jz A w0 s i y).det‖ ^ 2)) ∘ (A.chart i).symm)
      (A.chart i x) := by
  have hO := bsB_O_open A (De := De) hD i
  have hxO := bsB_O_mem A hx hi
  refine ⟨(A.smooth_ph _ i).contDiffAt ((A.chart i).open_target.mem_nhds hxO.1), ?_, ?_⟩
  · have hne : ((fun y => (σ i y)⁻¹) ∘ (A.chart i).symm) (A.chart i x) ≠ 0 := by
      simp only [Function.comp_apply, (A.chart i).left_inv hi]
      exact inv_ne_zero (bsA_ne_of_tr A hσ.1.2 hx hi (A.mem_pick x) (hσ.2 x hx))
    exact bsB_logsq hO hxO (bsB_inv_diffOn A hσ i) hne
  · have hc : ContDiffAt ℂ ∞ ((fun y => (jz A w0 s i y).det) ∘ (A.chart i).symm) (A.chart i x) := by
      refine (contDiffAt_det_jz A hD hF x hx i hi).congr_of_eventuallyEq ?_
      filter_upwards [(A.chart i).open_target.mem_nhds hxO.1] with v hv
      simp [bsB_jz_eq A hv]
    have h2 : ContDiffAt ℝ ∞ (fun v => ‖((fun y => (jz A w0 s i y).det) ∘ (A.chart i).symm) v‖ ^ 2)
        (A.chart i x) := (hc.restrict_scalars ℝ).norm_sq ℂ
    have hne : ((fun y => (jz A w0 s i y).det) ∘ (A.chart i).symm) (A.chart i x) ≠ 0 := by
      simp only [Function.comp_apply, (A.chart i).left_inv hi]
      exact jz_det_ne A hD hF x hx i hi
    exact h2.log (by positivity)
end ReciprocityTheory.L2DbarEstimates.Y
