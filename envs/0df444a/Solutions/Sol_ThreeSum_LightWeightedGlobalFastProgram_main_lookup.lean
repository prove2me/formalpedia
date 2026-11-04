-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalFastProgram.main_lookup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:45:23.061846+00:00
-- url     : https://prove2.me/submissions/aa4bf7f1-b74f-41f7-8f9e-abd8cbc2aa6c

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_Submission_ThreeSum_LightColorScanHost
import Definitions.Def_Submission_Weighted_Global_LightTernaryFastProgram

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalFastProgram
open Light
set_option maxRecDepth 24000
namespace ThreeSum.LightWeightedGlobalFastProgram
theorem _root_.solution (M radix p K κ : ℕ) (color : Program) (colorMain : ℕ) :
    (program M radix p K κ color colorMain)[mainEntry color]?=some (body (hostEntry color)) := by
  unfold program mainEntry
  rw [List.getElem?_append_right (by rw [parameterLibrary_length]; omega),parameterLibrary_length]
  rw [show 54+color.length-(52+color.length)=2 by omega]
  rfl
end ThreeSum.LightWeightedGlobalFastProgram
