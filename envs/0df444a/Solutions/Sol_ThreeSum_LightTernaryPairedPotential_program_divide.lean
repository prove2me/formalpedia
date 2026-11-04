-- Prove2me | solution 1 for ThreeSum.LightTernaryPairedPotential.program_divide
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:51:42.125711+00:00
-- url     : https://prove2.me/submissions/2ccb9890-c47c-49f5-8e96-a56b4f9c1c36

import Definitions.Def_Submission_ThreeSum_TernaryPairedColumnEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPotential
open Light LightTernaryPairedPolynomial TernaryPairedColumnEnumeration TernaryPairedTensor
open scoped BigOperators
namespace ThreeSum.LightTernaryPairedPotential
theorem _root_.solution (m : ℕ) : (program m)[4]?=some LightSmallDivide.body := rfl
end ThreeSum.LightTernaryPairedPotential
