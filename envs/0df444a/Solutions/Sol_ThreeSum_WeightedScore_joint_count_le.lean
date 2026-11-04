-- Prove2me | solution 1 for ThreeSum.WeightedScore.joint_count_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:45:16.841918+00:00
-- url     : https://prove2.me/submissions/43125ba2-a398-4ce6-912d-5383280000ed

import Definitions.Def_Submission_ThreeSum_WeightedModuli
import Definitions.Def_Submission_ThreeSum_ModuloCounts
import Definitions.Def_Submission_ThreeSum_WeightedScore
import Theorems.Thm_ThreeSum_WeightedScore_count_mono_dvd
import Theorems.Thm_ThreeSum_WeightedScore_base_dvd_joint

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedScore
open Finset Arithmetic ModuloCounts WeightedModuli
open scoped BigOperators
namespace ThreeSum.WeightedScore
theorem _root_.solution (q p nA nB nC : ℕ) (a b c : ℕ → ℤ) :
    count (joint q p) nA nB nC a b c ≤ count q nA nB nC a b c :=
  count_mono_dvd (base_dvd_joint q p) nA nB nC a b c
end ThreeSum.WeightedScore
