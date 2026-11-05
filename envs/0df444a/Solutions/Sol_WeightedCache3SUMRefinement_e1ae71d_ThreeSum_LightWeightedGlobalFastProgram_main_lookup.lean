-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalFastProgram.main_lookup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T14:46:57.708208+00:00
-- url     : https://prove2.me/submissions/70298131-9bed-4d81-80da-b739d8c920db

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_Submission_ThreeSum_LightColorScanHost
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryFastProgram

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalFastProgram
open Light
set_option maxRecDepth 24000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalFastProgram
theorem _root_.solution (M radix p K κ : ℕ) (color : Program) (colorMain : ℕ) :
    (program M radix p K κ color colorMain)[mainEntry color]?=some (body (hostEntry color)) := by
  unfold program mainEntry
  rw [List.getElem?_append_right (by rw [parameterLibrary_length]; omega),parameterLibrary_length]
  rw [show 54+color.length-(52+color.length)=2 by omega]
  rfl
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalFastProgram
