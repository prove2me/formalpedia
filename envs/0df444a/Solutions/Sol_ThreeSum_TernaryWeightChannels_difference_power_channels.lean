-- Prove2me | solution 1 for ThreeSum.TernaryWeightChannels.difference_power_channels
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:34:48.812245+00:00
-- url     : https://prove2.me/submissions/a140689e-b1e7-4f18-a2d9-54ea5f33c670

import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWeightChannels
open Finset LightFixedArithmetic TernaryJointType TernaryWeightedPhysicalSources
open scoped BigOperators
namespace ThreeSum.TernaryWeightChannels
theorem _root_.solution (k : ℕ) (b c : ℤ) :
    (c-b)^k=∑ j∈range (k+1), (k.choose j : ℤ)*(-b)^j*c^(k-j) := by
  have h := add_pow (-b) c k
  rw [show -b+c=c-b by ring] at h
  rw [h]
  apply sum_congr rfl
  intro j hj
  ring
end ThreeSum.TernaryWeightChannels
