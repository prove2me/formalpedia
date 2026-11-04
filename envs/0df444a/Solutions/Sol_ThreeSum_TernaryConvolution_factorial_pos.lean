-- Prove2me | solution 1 for ThreeSum.TernaryConvolution.factorial_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:35:23.30848+00:00
-- url     : https://prove2.me/submissions/062dc28c-089c-49b8-9ad1-0310cb18b68d

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Mathlib.Algebra.BigOperators.Finprod
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Theorems.Thm_ThreeSum_TernaryConvolution_factorial_eq_power_two

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryConvolution
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryConvolution
theorem _root_.solution {N : ℕ} (A : TritWord N) : 0<factorial A := by
  rw [factorial_eq_power_two]
  positivity
end ThreeSum.TernaryConvolution
