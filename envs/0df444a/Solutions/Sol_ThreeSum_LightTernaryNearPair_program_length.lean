-- Prove2me | solution 1 for ThreeSum.LightTernaryNearPair.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:10:14.823732+00:00
-- url     : https://prove2.me/submissions/e81b8224-1b38-468c-8d46-12b1851c181b

import Definitions.Def_Submission_ThreeSum_LightTernaryNearSourceWords
import Definitions.Def_Submission_ThreeSum_LightTernaryNearPair

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryNearPair
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
namespace ThreeSum.LightTernaryNearPair
theorem _root_.solution : program.length=19 := rfl
end ThreeSum.LightTernaryNearPair
