-- Prove2me | solution 1 for ThreeSum.LightTernaryRank.partialRank_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:30:21.55788+00:00
-- url     : https://prove2.me/submissions/cf46cee9-51f8-476f-a132-d31d96d6c922

import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryRank

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryRank
open Light Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.LightSubsetAddress
namespace ThreeSum.LightTernaryRank
theorem _root_.solution (N m j : ℕ) :
    partialRank N m (j+1)=partialRank N m j+digitAt N m j := sum_range_succ _ _
end ThreeSum.LightTernaryRank
