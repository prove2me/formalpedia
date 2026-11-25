-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.holomorphicOn_finiteCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:24:45.061147+00:00
-- url     : https://prove2.me/submissions/8ec8ba14-8b65-428f-b02d-82dcb1291304

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
theorem _root_.solution : p1.HoloOn (Set.range ((↑) : ℂ → OnePoint ℂ)) crd0 := by
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · intro w _
    exact projLine_analyticAt_apply_zero w
  · intro w hw
    have e : crd0 ∘ (p1.chart (1 : Fin 2)).symm = fun v : Fin 1 → ℂ => (v 0)⁻¹ := by
      funext v
      exact finiteCoord_projLineChart1_symm v
    rw [e]
    exact projLine_analyticAt_inv_apply_zero (projLineChart1_symm_mem_range.1 hw.2)
end ReciprocityTheory.AnForm.M
