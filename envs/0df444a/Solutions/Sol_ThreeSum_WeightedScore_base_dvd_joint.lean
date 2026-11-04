-- Prove2me | solution 1 for ThreeSum.WeightedScore.base_dvd_joint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:40:11.93232+00:00
-- url     : https://prove2.me/submissions/b1eba522-8570-4a9e-9c80-eec75caf72e5

import Definitions.Def_Submission_ThreeSum_WeightedModuli
import Definitions.Def_Submission_ThreeSum_ModuloCounts
import Definitions.Def_Submission_ThreeSum_WeightedScore

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedScore
open Finset Arithmetic ModuloCounts WeightedModuli
open scoped BigOperators
namespace ThreeSum.WeightedScore
theorem _root_.solution (q p : ℕ) : q ∣ joint q p := by
  unfold joint
  split
  · exact dvd_refl q
  · exact dvd_mul_right q p
end ThreeSum.WeightedScore
