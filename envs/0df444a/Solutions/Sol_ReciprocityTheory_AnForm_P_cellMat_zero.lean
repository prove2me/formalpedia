-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.cellMat_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:24:00.553234+00:00
-- url     : https://prove2.me/submissions/8a835d46-ec4e-44c9-8eb2-25545dd6b6b7

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDens
import Theorems.Thm_ReciprocityTheory_AnForm_P_cellMat_eq
import Theorems.Thm_ReciprocityTheory_AnForm_P_zMat_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open MeasureTheory
noncomputable section
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution : CellMatZeroStatement := by
  intro N
  have hz : zMat N 0 = 0 := by
    ext i j
    rw [zMat_apply]
    split_ifs <;> rfl
  rw [cellMat_eq, hz]
  rcases N with _ | n
  · exact Subsingleton.elim _ _
  · rw [Finset.sum_range_succ']
    simp
end ReciprocityTheory.AnForm.P
