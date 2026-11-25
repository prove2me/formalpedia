-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.regMax_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:12:01.192376+00:00
-- url     : https://prove2.me/submissions/16405845-28ab-4721-a19a-59a314681a7f

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_fderiv_sum
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_fderiv2_bound
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_add_const
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_contDiff
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_convex
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_eq_of_dom
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_ge
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_le
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_mono
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_update


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : RegMaxStatement := by
  intro ι _ _ _
  refine ⟨fun η hη => ⟨regMax_contDiff hη, regMax_convex η, regMax_mono η,
    fun t => ⟨regMax_ge η t, regMax_le hη.le t⟩,
    fun t i hi => regMax_eq_of_dom hη.le t i hi,
    fun t j k s hkj htj hs => regMax_update hη.le t j k s hkj htj hs,
    fun t c => regMax_add_const η t c,
    fun t => regMax_fderiv_sum hη t⟩, ?_⟩
  obtain ⟨C, hC⟩ := regMax_fderiv2_bound (ι := ι)
  exact ⟨C, fun η hη t i j => hC η hη t _ _ (by simp [Pi.norm_single]) (by simp [Pi.norm_single])⟩
end ReciprocityTheory.AnForm.A
