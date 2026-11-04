-- Prove2me | solution 1 for ThreeSumApsp.FromClaims.cast_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:17:19.512137+00:00
-- url     : https://prove2.me/submissions/451ed6bd-219f-4c1d-bf08-fd16e60108e4

import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_FromClaims_Bounds

set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.FromClaims
open ThreeSumApsp.WordRam
open EndStatement (Instr)
namespace ThreeSumApsp.FromClaims
theorem _root_.solution (N c : ℕ) : ((N ^ c : ℕ) : ℝ) = (N : ℝ) ^ ((c : ℕ) : ℝ) := by
  rw [Real.rpow_natCast]
  push_cast
  rfl
end ThreeSumApsp.FromClaims
