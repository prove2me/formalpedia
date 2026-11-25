-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.holomorphicOn_infiniteCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:24:20.789429+00:00
-- url     : https://prove2.me/submissions/88e1fd94-a7a0-4019-ba19-05a198b61d8c

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
theorem _root_.solution : p1.HoloOn {x | x ≠ ((0 : ℂ) : OnePoint ℂ)} crd1 := by
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · intro w hw
    have e : crd1 ∘ (p1.chart (0 : Fin 2)).symm = fun v : Fin 1 → ℂ => (v 0)⁻¹ := by
      funext v
      rfl
    rw [e]
    exact projLine_analyticAt_inv_apply_zero (projLineChart0_symm_ne_zero.1 hw.2)
  · intro w _
    have e : crd1 ∘ (p1.chart (1 : Fin 2)).symm = fun v : Fin 1 → ℂ => v 0 := by
      funext v
      exact infiniteCoord_projLineChart1_symm v
    rw [e]
    exact projLine_analyticAt_apply_zero w
end ReciprocityTheory.AnForm.M
