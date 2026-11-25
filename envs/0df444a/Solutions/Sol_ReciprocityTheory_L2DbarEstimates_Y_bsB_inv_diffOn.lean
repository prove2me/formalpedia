-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsB_inv_diffOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:31:26.607864+00:00
-- url     : https://prove2.me/submissions/48e8ecef-2503-4970-968f-4968e96d12c8

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_ne_of_tr


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
theorem _root_.solution (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (i : ι) :
    DifferentiableOn ℂ ((fun y => (σ i y)⁻¹) ∘ (A.chart i).symm)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De) := by
  have h := (hσ.1.1 i).inv (fun v hv =>
    bsA_ne_of_tr A hσ.1.2 hv.2 ((A.chart i).map_target hv.1) (A.mem_pick _) (hσ.2 _ hv.2))
  exact h.congr fun v _ => rfl
end ReciprocityTheory.L2DbarEstimates.Y
