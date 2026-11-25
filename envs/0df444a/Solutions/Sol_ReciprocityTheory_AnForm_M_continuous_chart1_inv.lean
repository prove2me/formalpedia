-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.continuous_chart1_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:07:05.841602+00:00
-- url     : https://prove2.me/submissions/1194ea6b-8c8f-472c-9e43-bbde8f097d94

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology
noncomputable section
open scoped Classical
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution :
    Continuous (fun w : Fin 1 → ℂ => if w 0 = 0 then (∞ : OnePoint ℂ) else (((w 0)⁻¹ : ℂ) : OnePoint ℂ)) := by
  set g : ℂ → OnePoint ℂ := fun z => if z = 0 then (∞ : OnePoint ℂ) else ((z⁻¹ : ℂ) : OnePoint ℂ)
    with hg_def
  have hg : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z = 0
    · subst hz
      have hf0 : g 0 = ∞ := by simp [hg_def]
      show Tendsto g (𝓝 0) (𝓝 (g 0))
      rw [← nhdsNE_sup_pure (0 : ℂ)]
      refine Tendsto.sup ?_ (tendsto_pure_nhds g 0)
      have h1 : Tendsto (fun w : ℂ => ((w⁻¹ : ℂ) : OnePoint ℂ)) (𝓝[≠] 0) (𝓝 ∞) := by
        refine OnePoint.tendsto_coe_infty.comp ?_
        rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
        exact Filter.tendsto_inv₀_nhdsNE_zero
      rw [hf0]
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with w hw
      have hw' : w ≠ 0 := hw
      simp [hg_def, hw']
    · have h1 : ContinuousAt (fun w : ℂ => ((w⁻¹ : ℂ) : OnePoint ℂ)) z :=
        OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hz)
      refine h1.congr ?_
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      simp [hg_def, hw]
  exact hg.comp (continuous_apply 0)
end ReciprocityTheory.AnForm.M
