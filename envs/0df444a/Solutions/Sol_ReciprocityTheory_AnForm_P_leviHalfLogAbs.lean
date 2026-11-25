-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.leviHalfLogAbs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:14:52.177733+00:00
-- url     : https://prove2.me/submissions/4677146b-3ecd-4afb-90ac-051a50bad3d5

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDens
import Theorems.Thm_ReciprocityTheory_AnForm_P_leviForm_half_log_abs_of_fderiv_eq_zero


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
theorem _root_.solution : LeviHalfLogAbsStatement := by
  intro ι _ f z hf hz hd w
  exact leviForm_half_log_abs_of_fderiv_eq_zero f z hf hz hd w
end ReciprocityTheory.AnForm.P
