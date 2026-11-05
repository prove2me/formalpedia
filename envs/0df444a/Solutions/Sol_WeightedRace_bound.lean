-- Prove2me | solution 1 for WeightedRace.bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T05:36:03.34023+00:00
-- url     : https://prove2.me/submissions/a4154e11-2af5-4cd2-9b16-e538c67715cd

import Definitions.Def_Submission_Weighted_Global_TernaryFinalSolver
import Definitions.Def_Submission_Weighted
import Theorems.Thm_ThreeSum_weighted_solvedInTime_96013971_50000000


set_option autoImplicit false
open WeightedRace
namespace WeightedRace
theorem _root_.solution : EndStatement.ThreeSum.SolvedInTime (96013971 / 50000000 : Rat) :=
  ThreeSum.weighted_solvedInTime_96013971_50000000
end WeightedRace
