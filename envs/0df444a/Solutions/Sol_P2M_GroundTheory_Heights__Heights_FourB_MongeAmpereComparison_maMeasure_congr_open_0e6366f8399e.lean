-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_maMeasure_congr_open_0e6366f8399e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:45:54.799883+00:00
-- url     : https://prove2.me/submissions/2a9fe08c-6f69-491c-a8df-93bb7506a8eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PMongeAmpereComparison
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_maMeasure_eq_sum
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison
namespace GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison
theorem _root_.solution {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas e X) (Φ Ψ : Fin e → LocPot X) {S : Set X} (hS : IsOpen S)
    (h : ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ S →
      locDens A Φ j y = locDens A Ψ j y) :
    maMeasure A Φ S = maMeasure A Ψ S := by
  by_cases hne : Nonempty (ChartPartition A)
  · rw [maMeasure_eq_sum A Φ hne, maMeasure_eq_sum A Ψ hne]
    simp only [Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold chartMeasure
    have hTm := (A.chart j).open_target.measurableSet
    have hsm : AEMeasurable (A.chart j).symm (volume.restrict (A.chart j).target) :=
      (A.chart j).continuousOn_symm.aemeasurable hTm
    rw [Measure.map_apply_of_aemeasurable (hsm.mono_ac (withDensity_absolutelyContinuous _ _))
        hS.measurableSet,
      Measure.map_apply_of_aemeasurable (hsm.mono_ac (withDensity_absolutelyContinuous _ _))
        hS.measurableSet, withDensity_apply', withDensity_apply', Measure.restrict_restrict' hTm]
    have hV : IsOpen ((A.chart j).symm ⁻¹' S ∩ (A.chart j).target) := by
      rw [Set.inter_comm]
      exact (A.chart j).isOpen_inter_preimage_symm hS
    refine setLIntegral_congr_fun hV.measurableSet fun y hy => ?_
    simp only [h j y hy.2 hy.1]
  · unfold maMeasure
    rw [dif_neg hne, dif_neg hne]
end GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison
