-- Prove2me | solution 1 for ThreeSum.LightWeightedSourceCountHost.sourceArgs_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:21:07.148682+00:00
-- url     : https://prove2.me/submissions/35bb3847-28e8-4e8c-ae20-271f6168b798

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
import Definitions.Def_Submission_Weighted_SourceCountHost

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedSourceCountHost
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
namespace ThreeSum.LightWeightedSourceCountHost
theorem _root_.solution (a b c e f g h i j k l m n o p q r s t u w x y : ℕ) :
    (sourceArgs a b c e f g h i j k l m n o p q r s t u w x y).length=23 := rfl
end ThreeSum.LightWeightedSourceCountHost
