-- Prove2me | solution 1 for ThreeSum.LightTernarySourceCountHost.sourceArgs_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:25:42.568415+00:00
-- url     : https://prove2.me/submissions/b7462aeb-4b6d-4153-a578-6a32eb0e6a16

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_Submission_ThreeSum_LightTernaryCountFrontend
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
import Definitions.Def_Submission_ThreeSum_LightTernarySourceCountHost

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernarySourceCountHost
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
namespace ThreeSum.LightTernarySourceCountHost
theorem _root_.solution (a b c e f g h i j k l m n o p q r s t u w x y : ℕ) :
    (sourceArgs a b c e f g h i j k l m n o p q r s t u w x y).length=23 := rfl
end ThreeSum.LightTernarySourceCountHost
