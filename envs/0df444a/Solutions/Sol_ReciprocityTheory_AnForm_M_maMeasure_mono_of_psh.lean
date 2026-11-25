-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.maMeasure_mono_of_psh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:09:23.878317+00:00
-- url     : https://prove2.me/submissions/c66e7687-ceb4-4d48-8725-ade310277a05

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDens_le_add


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
theorem _root_.solution {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas e X) (Φ Θ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (hΦp : ∀ i, IsPsh A (Φ i))
    (hΘ : ∀ i, IsPotential A (Θ i)) (hΘp : ∀ i, IsPsh A (Θ i)) :
    maMeasure A Φ ≤ maMeasure A (fun i => Φ i + Θ i) := by
  unfold maMeasure
  split_ifs with h
  · rw [Measure.le_iff]
    intro s hs
    simp only [Measure.coe_finset_sum, Finset.sum_apply]
    refine Finset.sum_le_sum fun j _ => ?_
    have hT := (A.chart j).open_target.measurableSet
    have hsm : AEMeasurable (A.chart j).symm (volume.restrict (A.chart j).target) :=
      (A.chart j).continuousOn_symm.aemeasurable hT
    have hle : (volume.restrict (A.chart j).target).withDensity (fun y =>
          ENNReal.ofReal (h.some.χ j ((A.chart j).symm y) * locDens A Φ j y)) ≤
        (volume.restrict (A.chart j).target).withDensity (fun y =>
          ENNReal.ofReal (h.some.χ j ((A.chart j).symm y) * locDens A (fun i => Φ i + Θ i) j y)) := by
      refine withDensity_mono ?_
      filter_upwards [ae_restrict_mem hT] with y hy
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (locDens_le_add A Φ Θ hΦ hΦp hΘ hΘp j hy) (h.some.nonneg j _))
    rw [Measure.map_apply_of_aemeasurable (hsm.mono_ac (withDensity_absolutelyContinuous _ _)) hs,
      Measure.map_apply_of_aemeasurable (hsm.mono_ac (withDensity_absolutelyContinuous _ _)) hs]
    exact Measure.le_iff'.1 hle _
  · exact le_rfl
end ReciprocityTheory.AnForm.M
