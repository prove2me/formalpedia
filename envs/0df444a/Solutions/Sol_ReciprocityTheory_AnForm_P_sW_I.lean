-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.sW_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:39.903395+00:00
-- url     : https://prove2.me/submissions/f5642d8f-5542-44ae-8f84-289d1e736434

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDens
import Theorems.Thm_ReciprocityTheory_AnForm_P_zMat_smul


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
open Matrix Polynomial
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (w : Pairs N → ℂ) :
    sW N hd m (Complex.I • w) = sW N hd m w := by
  simp [sW, zMat_smul, norm_mul]
end ReciprocityTheory.AnForm.P
