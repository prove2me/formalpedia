-- Prove2me | solution 1 for ThreeSum.TernaryPartialEuler.restrictedWeight_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:24:05.339735+00:00
-- url     : https://prove2.me/submissions/4d262463-034d-415f-b559-f8ce6c7deaf0

import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPartialEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryTransform
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryPartialEuler
theorem _root_.solution {N : ℕ} (S : Finset (Fin N)) (R : TritWord N)
    (i : Fin N) : restrictedWeight S R i≤2 := by
  have hi := (R i).isLt
  unfold restrictedWeight
  split <;> omega
end ThreeSum.TernaryPartialEuler
