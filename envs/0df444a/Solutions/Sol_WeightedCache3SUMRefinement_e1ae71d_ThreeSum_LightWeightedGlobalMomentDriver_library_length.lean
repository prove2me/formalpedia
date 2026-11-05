-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalMomentDriver.library_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:40:18.927194+00:00
-- url     : https://prove2.me/submissions/46a2af42-2bfb-446d-a408-34d5a9388118

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryMomentDriver

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalMomentDriver
open Light TernaryMomentSchedule
set_option maxHeartbeats 2000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalMomentDriver
theorem _root_.solution (xl yl zl xr yr zr : List ℤ) (steps : List (ℕ×ℕ)) :
    (library xl yl zl xr yr zr steps).length=139*steps.length := by
  induction steps with
  | nil => simp [library]
  | cons c cs ih =>
    simp only [library,ReportingHostRelocation.program,List.length_append,List.length_map,
      LightWeightedGlobalMomentSourceProgram.program_length,ih,List.length_cons]
    omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalMomentDriver

