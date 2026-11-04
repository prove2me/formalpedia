-- Prove2me | solution 1 for ThreeSum.TernaryLocalParameters.fixed_mixedFiber_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:13:30.268804+00:00
-- url     : https://prove2.me/submissions/72332b69-06de-45ce-98f8-bb14be3d75b2

import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformProjection
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
import Theorems.Thm_ThreeSum_TernaryLocalParameters_fixedPi_total
import Theorems.Thm_ThreeSum_TernaryLocalParameters_fixedPi_space
import Theorems.Thm_ThreeSum_TernaryLocalParameters_fixed_thirds
import Theorems.Thm_ThreeSum_TernaryLocalParameters_difference_choose_le_partition
import Theorems.Thm_ThreeSum_TernaryCoverUniformProjection_mixedFiber_uniform_card_le
import Theorems.Thm_ThreeSum_TernaryTypeLowerBound_partition_cap_le_prime


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryLocalParameters
open Finset TernaryJointType TernaryCoverLocal TernaryTypeLowerBound TernaryCoverUniformProjection
namespace ThreeSum.TernaryLocalParameters
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
end ThreeSum.TernaryLocalParameters
