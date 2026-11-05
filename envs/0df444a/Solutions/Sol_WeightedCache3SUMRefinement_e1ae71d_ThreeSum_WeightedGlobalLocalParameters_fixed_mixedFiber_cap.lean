-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalLocalParameters.fixed_mixedFiber_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:10:01.951566+00:00
-- url     : https://prove2.me/submissions/11764d6d-53c5-4f21-a77c-9a61e8f1d205

import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformProjection
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalLocalParameters
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalLocalParameters_fixedPi_total
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalLocalParameters_fixedPi_space
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalLocalParameters_fixed_thirds
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalLocalParameters_difference_choose_le_partition
import Theorems.Thm_ThreeSum_TernaryCoverUniformProjection_mixedFiber_uniform_card_le
import Theorems.Thm_ThreeSum_TernaryTypeLowerBound_partition_cap_le_prime


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalLocalParameters
open Finset TernaryJointType TernaryCoverLocal TernaryTypeLowerBound TernaryCoverUniformProjection
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalLocalParameters
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
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalLocalParameters
