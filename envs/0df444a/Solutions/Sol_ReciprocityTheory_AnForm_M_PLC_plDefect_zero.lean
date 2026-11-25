-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLC.plDefect_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:06:05.356817+00:00
-- url     : https://prove2.me/submissions/c8c901b0-6a2e-4222-81d9-64ad7a2a70af

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurve
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLC_mInt_zero
import Theorems.Thm_ReciprocityTheory_AnForm_M_mIntConstPot


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff
noncomputable section
open ReciprocityTheory.AnForm.M.PLC
variable {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M.PLC
theorem _root_.solution (A : FinHolAtlas 1 X) (L : LocPot X) (s : X → X → ℂ) {r : ℕ}
    (m : Fin r → ℕ) (p : Fin r → X) : plDefect A L s m p (fun _ => 0) = 0 := by
  unfold plDefect
  have h0 : mInt A ![LocPot.ofFun fun _ => (0 : ℝ)] (logNormSec L s) = 0 :=
    mIntConstPot (e := 0) A 0 ![] _
  rw [h0, mInt_zero]
  simp
end ReciprocityTheory.AnForm.M.PLC
