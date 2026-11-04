-- Prove2me | solution 1 for ThreeSum.LightBalancedOffset.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:36:28.489963+00:00
-- url     : https://prove2.me/submissions/d27c64c2-fd7d-4452-8ccd-399bb6697310

import Definitions.Def_Submission_ThreeSum_LightCyclic
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Definitions.Def_Submission_ThreeSum_LightBalancedOffset

set_option autoImplicit false
open ThreeSum ThreeSum.LightBalancedOffset
open Light Karatsuba CyclicFold LightKaratsuba Finset
open scoped BigOperators
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightBalancedOffset
theorem _root_.solution (k p : ℕ) (hp : p ≤ 2^k) :
    time k p ≤ LightKaratsuba.time k + 226*2^k + 226 := by
  unfold time LightCyclic.combinedTime LightMinimum.time LightArray.linearTime
  omega
end ThreeSum.LightBalancedOffset
