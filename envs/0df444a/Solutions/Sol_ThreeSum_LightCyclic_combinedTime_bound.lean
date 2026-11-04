-- Prove2me | solution 1 for ThreeSum.LightCyclic.combinedTime_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:17:04.691196+00:00
-- url     : https://prove2.me/submissions/ffa2eea3-6426-4a9a-b08e-d80033057099

import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_KaratsubaInterface
import Definitions.Def_Submission_ThreeSum_LightCyclic

set_option autoImplicit false
open ThreeSum ThreeSum.LightCyclic
open Light Karatsuba CyclicFold LightKaratsuba
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightCyclic
theorem _root_.solution (k p : ℕ) (hp : p ≤ 2^k) :
    combinedTime k p ≤ LightKaratsuba.time k + 106 * 2^k + 106 := by
  unfold combinedTime LightArray.linearTime
  omega
end ThreeSum.LightCyclic
