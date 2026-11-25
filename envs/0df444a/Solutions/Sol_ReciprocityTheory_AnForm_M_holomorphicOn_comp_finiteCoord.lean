-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.holomorphicOn_comp_finiteCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:24:24.425098+00:00
-- url     : https://prove2.me/submissions/15132863-d8b5-412d-ba13-8f8d33163799

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_analyticAt_apply_zero
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_analyticAt_inv_apply_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {B : Set ℂ} {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F B) :
    p1.HoloOn (projectiveLineChartAtZero.source ∩ projectiveLineChartAtZero ⁻¹' {w | w 0 ∈ B}) (fun x => F (crd0 x)) := by
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · intro w hw
    have hB : w 0 ∈ B := hw.2.2
    have h := AnalyticAt.comp (g := F) (f := fun v : Fin 1 → ℂ => v 0) (x := w) (hF (w 0) hB)
      (projLine_analyticAt_apply_zero w)
    exact h
  · intro w hw
    have hne : w 0 ≠ 0 := projLineChart1_symm_mem_range.1 hw.2.1
    have hB : (w 0)⁻¹ ∈ B := by
      have h2 : crd0 (projectiveLineChartAtInfinity.symm w) ∈ B := hw.2.2
      rwa [finiteCoord_projLineChart1_symm] at h2
    have e : (fun x => F (crd0 x)) ∘ (p1.chart (1 : Fin 2)).symm =
        F ∘ (fun v : Fin 1 → ℂ => (v 0)⁻¹) := by
      funext v
      exact congrArg F (finiteCoord_projLineChart1_symm v)
    rw [e]
    have h := AnalyticAt.comp (g := F) (f := fun v : Fin 1 → ℂ => (v 0)⁻¹) (x := w) (hF _ hB)
      (projLine_analyticAt_inv_apply_zero hne)
    exact h
end ReciprocityTheory.AnForm.M
