-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fn_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:10:55.486219+00:00
-- url     : https://prove2.me/submissions/398e6db5-14be-4874-9b84-6b92c38994f6

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_symm_aemeas

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
theorem _root_.solution (i : ι) :
    Measure.map (A.chart i).symm ((volume.restrict (A.chart i).target).withDensity (fnRho A i)) =
      A.mu.restrict (A.chart i).source := by
  have hsymm : AEMeasurable (A.chart i).symm
      ((volume.restrict (A.chart i).target).withDensity (fnRho A i)) :=
    (fn_symm_aemeas A i).mono_ac (withDensity_absolutelyContinuous _ _)
  refine Measure.ext fun t ht => ?_
  rw [Measure.map_apply_of_aemeasurable hsymm ht, withDensity_apply' _ _,
    Measure.restrict_restrict' (A.chart i).open_target.measurableSet, Measure.restrict_apply ht,
    A.mu_chart i _ (ht.inter (A.chart i).open_source.measurableSet) Set.inter_subset_right,
    Set.inter_comm t (A.chart i).source, (A.chart i).image_source_inter_eq', Set.inter_comm]
  rfl
end ReciprocityTheory.L2DbarEstimates.Y
