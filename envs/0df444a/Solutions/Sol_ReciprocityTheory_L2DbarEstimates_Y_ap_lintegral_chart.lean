-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.ap_lintegral_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:30:53.552857+00:00
-- url     : https://prove2.me/submissions/3d7c7662-65a5-4f56-b27a-49dcb5fba4c3

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeW
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeI

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
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (A : WeightedAtlas n Y ι La) (i : ι) (g : Y → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y in (A.chart i).source, g y ∂A.mu =
      ∫⁻ v in (A.chart i).target, g ((A.chart i).symm v) *
        ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))) := by
  have htm : MeasurableSet (A.chart i).target := (A.chart i).open_target.measurableSet
  have hsm : MeasurableSet (A.chart i).source := (A.chart i).open_source.measurableSet
  have hsymm : AEMeasurable (A.chart i).symm (volume.restrict (A.chart i).target) :=
    (A.chart i).continuousOn_symm.aemeasurable htm
  have hρm : AEMeasurable (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))))
      (volume.restrict (A.chart i).target) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      (Real.continuous_exp.comp_continuousOn (A.smooth_ph A.kap i).continuousOn)).aemeasurable htm
  have hsymm' : AEMeasurable (A.chart i).symm ((volume.restrict (A.chart i).target).withDensity
      (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))))) :=
    hsymm.mono_ac (withDensity_absolutelyContinuous _ _)
  have hmeas : A.mu.restrict (A.chart i).source = Measure.map (A.chart i).symm
      ((volume.restrict (A.chart i).target).withDensity
        (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))))) := by
    ext s hs
    rw [Measure.restrict_apply hs, Measure.map_apply_of_aemeasurable hsymm' hs,
      withDensity_apply' _ _, Measure.restrict_restrict' htm,
      A.mu_chart i _ (hs.inter hsm) Set.inter_subset_right, Set.inter_comm s (A.chart i).source,
      (A.chart i).image_source_inter_eq', Set.inter_comm (A.chart i).target]
  rw [hmeas, lintegral_map' hg.aemeasurable hsymm']
  refine (lintegral_withDensity_eq_lintegral_mul₀ hρm (hg.comp_aemeasurable hsymm)).trans
    (lintegral_congr fun v => ?_)
  simp only [Pi.mul_apply, Function.comp]
  ring
end ReciprocityTheory.L2DbarEstimates.Y
