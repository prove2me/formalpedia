-- Prove2me | solution 1 for ThreeSum.WeightedGlobalLocalParameters.fixed_mixedFiber_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:14:17.44194+00:00
-- url     : https://prove2.me/submissions/52534d67-7aa3-4397-b420-1331c36851d1

import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformProjection
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
import Theorems.Thm_ThreeSum_WeightedGlobalLocalParameters_fixedPi_total
import Theorems.Thm_ThreeSum_WeightedGlobalLocalParameters_fixedPi_space
import Theorems.Thm_ThreeSum_WeightedGlobalLocalParameters_fixed_thirds
import Theorems.Thm_ThreeSum_WeightedGlobalLocalParameters_difference_choose_le_partition
import Theorems.Thm_ThreeSum_TernaryCoverUniformProjection_mixedFiber_uniform_card_le
import Theorems.Thm_ThreeSum_TernaryTypeLowerBound_partition_cap_le_prime


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalLocalParameters
open Finset TernaryJointType TernaryCoverLocal TernaryTypeLowerBound TernaryCoverUniformProjection
namespace ThreeSum.WeightedGlobalLocalParameters
theorem _root_.solution (m p : ℕ) [Fact p.Prime] (hp : 4 < p)
    (hP : (vertices (fixedLength m) (fixedPi m)).card*
      (2^(fixedPi m 1)*3^(fixedPi m 2)) ≤ p^2)
    {a b : ZMod p} (hab : a ≠ 0 ∨ b ≠ 0) (q : Fin (fixedLength m) → ZMod p) :
    (TernaryCoverGenericProjection.mixedFiber (fixedAlpha m) (fixedPi m) a b q).card ≤ p := by
  apply mixedFiber_uniform_card_le (fixedAlpha m) (fixedPi m) (fixed_thirds m)
    (fixedPi_total m) (fixedPi_space m) hp hP
  · exact (difference_choose_le_partition m).trans
      (partition_cap_le_prime (fixedPi m) (fixedPi_total m) (fixedPi_space m) p hP)
  · exact hab
end ThreeSum.WeightedGlobalLocalParameters
