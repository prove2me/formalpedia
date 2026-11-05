-- Prove2me | solution 1 for Race.bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T05:36:04.641422+00:00
-- url     : https://prove2.me/submissions/2ae83495-ccd1-42e2-9123-3d9fc532bf4c

import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_Weighted
import Definitions.Def_Submission
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryTime_bound
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceValues_bound
import Theorems.Thm_WeightedRace_bound


set_option autoImplicit false

namespace Race
theorem _root_.solution :
    EndStatement.ThreeSum.SolvedInTime ((96013971 : Rat) / 50000000) :=
  WeightedRace.bound
end Race
