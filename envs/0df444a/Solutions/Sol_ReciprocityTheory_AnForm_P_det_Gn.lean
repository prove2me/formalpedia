-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.det_Gn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:16:05.517825+00:00
-- url     : https://prove2.me/submissions/f1585032-52cd-459c-93e3-5ae30adeadd6

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Theorems.Thm_ReciprocityTheory_AnForm_P_det_tL_lower
import Theorems.Thm_ReciprocityTheory_AnForm_P_det_tL_upper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open Polynomial Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) :
    (Gn N hd m hm v).det = (Gm N hd m hm v).det := by
  rw [Gn, det_mul, det_mul, det_tL_upper, det_tL_lower, one_mul, mul_one]
end ReciprocityTheory.AnForm.P
