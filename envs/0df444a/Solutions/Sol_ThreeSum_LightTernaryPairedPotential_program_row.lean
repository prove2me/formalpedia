-- Prove2me | solution 1 for ThreeSum.LightTernaryPairedPotential.program_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:51:38.132502+00:00
-- url     : https://prove2.me/submissions/e8a0deed-91e5-4ee3-b19d-03ad4eebd54f

import Definitions.Def_Submission_ThreeSum_TernaryPairedColumnEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPotential
open Light LightTernaryPairedPolynomial TernaryPairedColumnEnumeration TernaryPairedTensor
open scoped BigOperators
namespace ThreeSum.LightTernaryPairedPotential
theorem _root_.solution (m : ℕ) : (program m)[2]?=some (LightWeightRow.body 3) := rfl
end ThreeSum.LightTernaryPairedPotential
