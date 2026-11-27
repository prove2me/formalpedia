-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_projectiveLine_current_smoothPotForm_9d3ab80351cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:53:29.130622+00:00
-- url     : https://prove2.me/submissions/6a12dccc-4889-4ffd-a558-75077dd705fb

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_projectiveLine_constantSystem_uT_d139ada671b2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_thetaOmega_p1Data___77a040157c61
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_thetaOmega_p1Data_pot_631a1bd82bf8
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_isPlurisubharmonic
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_isSmoothPotential
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open MeasureTheory Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot mInt MIntegrable)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ThGe ell errE)
noncomputable section
variable {D : ℕ} {X : Type*} [TopologicalSpace X]
open ReciprocityTheory.AnForm.M (p1 fsPot projLine_isSmoothPotential projLine_isPlurisubharmonic)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData projLine_fubiniStudy_isPosPot)
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
theorem _root_.solution (t : ℝ) :
    IsSmoothPotForm p1 projLineChartData.Yo projLineChartData.r projectiveLineKaehler 0 (thetaOmega projLineChartData) (projectiveLineConstantSystem.uT t) := by
  rw [projectiveLine_constantSystem_uT]
  refine ⟨⟨thetaOmega_p1Data_pot, ?_, ?_, fun _ => contDiffOn_const, fun _ _ => le_rfl,
    fun _ _ => by simp, ?_, Or.inl fun _ => contDiffOn_const⟩, fun _ => contDiffOn_const⟩
  · intro x k y _ w
    rw [thetaOmega_p1Data_φ]
    exact le_rfl
  · intro x k y hy w
    rw [thetaOmega_p1Data_φ]
    have := projLine_isPlurisubharmonic x k y ⟨hy.1, hy.2.1.2⟩ w
    show -1 * levi (fsPot.φ x ∘ (p1.chart k).symm) y w ≤
      1 * levi (fsPot.φ x ∘ (p1.chart k).symm) y w
    linarith
  · intro x k y hy w
    have h : (potForm (thetaOmega projLineChartData) fun _ => (0 : ℝ)).φ x = fsPot.φ x := by
      funext z
      show (thetaOmega projLineChartData).φ x z + 0 = fsPot.φ x z
      rw [thetaOmega_p1Data_φ, add_zero]
    rw [h]
    exact projLine_isPlurisubharmonic x k y ⟨hy.1, hy.2.2.1.2⟩ w
end GroundTheory.Heights₂.Heights.AnalyticLimit
