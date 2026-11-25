-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fn_rho_aemeas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:54:58.66961+00:00
-- url     : https://prove2.me/submissions/9005f2b6-0778-4528-a711-e959c2880e94

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullB

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
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (i : ι) : AEMeasurable (fnRho A i) (volume.restrict (A.chart i).target) := by
  have h : ContinuousOn (fnRho A i) (A.chart i).target :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (Real.continuous_exp.comp_continuousOn (A.smooth_ph A.kap i).continuousOn)
  exact h.aemeasurable (A.chart i).open_target.measurableSet
end ReciprocityTheory.L2DbarEstimates.Y
