-- Prove2me | solution 1 for ThreeSum.LightBalancedOffset.offset_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:36:56.33917+00:00
-- url     : https://prove2.me/submissions/3f7e7bf9-511b-49ba-83cc-3e17e65d1136

import Definitions.Def_Submission_ThreeSum_LightCyclic
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Definitions.Def_Submission_ThreeSum_LightBalancedOffset
import Theorems.Thm_ThreeSum_LightMinimum_least_lt


set_option autoImplicit false
open ThreeSum ThreeSum.LightBalancedOffset
open Light Karatsuba CyclicFold LightKaratsuba Finset
open scoped BigOperators
namespace ThreeSum.LightBalancedOffset
theorem _root_.solution {p : ℕ} [NeZero p] (F H : ZMod p → ℕ) : offset F H < p :=
  LightMinimum.least_lt _ (Nat.pos_of_ne_zero (NeZero.ne p))
end ThreeSum.LightBalancedOffset
