-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.generating_polynomials
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:40:56.589778+00:00
-- url     : https://prove2.me/submissions/1aa0bb63-373b-4e01-ba91-59772dee0c57

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
theorem _root_.solution : bankArg=1+y^512+y^1025 ∧
    queryArg1=1+z^512 ∧ queryArg2=1+z^513+z^1025 := ⟨rfl,rfl,rfl⟩
end ThreeSum.WeightedGlobalParameters
