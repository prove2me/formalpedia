-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.map_withDensity_integrable_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:22:11.443793+00:00
-- url     : https://prove2.me/submissions/c695a99f-b0fe-4742-a283-4fb2577f472b

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Set Filter Topology
open scoped ContDiff ENNReal NNReal
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {e : ℕ} {X : Type} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] {T : Set (Fin e → ℂ)} (hT : IsOpen T)
    {s : (Fin e → ℂ) → X} (hs : ContinuousOn s T) {w : (Fin e → ℂ) → ℝ} (hw : ContinuousOn w T)
    (hw0 : ∀ y ∈ T, 0 ≤ w y) {g : X → ℝ} (hg : Measurable g) :
    (Integrable g (((volume.restrict T).withDensity fun y => ENNReal.ofReal (w y)).map s) ↔
      IntegrableOn (fun y => g (s y) * w y) T) ∧
    ∫ x, g x ∂(((volume.restrict T).withDensity fun y => ENNReal.ofReal (w y)).map s) =
      ∫ y in T, g (s y) * w y := by
  have hTm : MeasurableSet T := hT.measurableSet
  have hsm : AEMeasurable s (volume.restrict T) := hs.aemeasurable hTm
  have hwm : AEMeasurable (fun y => (w y).toNNReal) (volume.restrict T) :=
    (hw.aemeasurable hTm).real_toNNReal
  have hν : ((volume.restrict T).withDensity fun y => ENNReal.ofReal (w y)) =
      (volume.restrict T).withDensity fun y => ((w y).toNNReal : ℝ≥0∞) := rfl
  have hsm' : AEMeasurable s ((volume.restrict T).withDensity fun y => ENNReal.ofReal (w y)) :=
    hsm.mono_ac (withDensity_absolutelyContinuous _ _)
  have hae : (fun y => (w y).toNNReal • g (s y)) =ᵐ[volume.restrict T] (fun y => g (s y) * w y) := by
    filter_upwards [ae_restrict_mem hTm] with y hy
    rw [NNReal.smul_def, Real.coe_toNNReal _ (hw0 y hy), smul_eq_mul, mul_comm]
  constructor
  · rw [integrable_map_measure hg.aestronglyMeasurable hsm', hν]
    exact (integrable_withDensity_iff_integrable_smul₀ hwm).trans (integrable_congr hae)
  · rw [integral_map hsm' hg.aestronglyMeasurable, hν, integral_withDensity_eq_integral_smul₀ hwm]
    exact integral_congr_ae hae
end ReciprocityTheory.AnForm.M
