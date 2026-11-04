-- Prove2me | solution 1 for ThreeSum.LightTernaryPairedPotential.program_digit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:51:41.017807+00:00
-- url     : https://prove2.me/submissions/487a18f3-a089-4e99-be10-6edea310b769

import Definitions.Def_Submission_ThreeSum_TernaryPairedColumnEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPotential
open Light LightTernaryPairedPolynomial TernaryPairedColumnEnumeration TernaryPairedTensor
open scoped BigOperators
namespace ThreeSum.LightTernaryPairedPotential
theorem _root_.solution (m : ℕ) : (program m)[3]?=some (LightRadixDigit.body 4) := rfl
end ThreeSum.LightTernaryPairedPotential
