-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.logMonoLocInt_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:32.946441+00:00
-- url     : https://prove2.me/submissions/d2eab742-75c2-4fd9-a61f-2c882c62a4a8

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogIntSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Theorems.Thm_ReciprocityTheory_AnForm_A_logCoordLocInt_thm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : LogMonoLocIntStatement := by
  intro D m
  exact locallyIntegrable_finset_sum (μ := volume) Finset.univ
    (f := fun i (z : Fin D → ℂ) => (m i : ℝ) * Real.log ‖z i‖)
    (fun i _ => (logCoordLocInt_thm D i).smul (m i : ℝ))
end ReciprocityTheory.AnForm.A
