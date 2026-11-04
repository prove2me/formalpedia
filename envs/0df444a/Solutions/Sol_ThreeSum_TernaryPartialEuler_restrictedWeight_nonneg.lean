-- Prove2me | solution 1 for ThreeSum.TernaryPartialEuler.restrictedWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:24:04.135545+00:00
-- url     : https://prove2.me/submissions/bc794137-7ed1-43ea-b86e-fd78d1ee8b75

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
    (i : Fin N) : 0≤restrictedWeight S R i := by
  unfold restrictedWeight
  split <;> positivity
end ThreeSum.TernaryPartialEuler
