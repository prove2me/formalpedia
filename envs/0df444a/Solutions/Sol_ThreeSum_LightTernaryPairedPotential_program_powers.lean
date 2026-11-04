-- Prove2me | solution 1 for ThreeSum.LightTernaryPairedPotential.program_powers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:51:37.104208+00:00
-- url     : https://prove2.me/submissions/b9c054e5-5415-498a-9b74-c5e73d7a4f2a

import Definitions.Def_Submission_ThreeSum_TernaryPairedColumnEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPotential
open Light LightTernaryPairedPolynomial TernaryPairedColumnEnumeration TernaryPairedTensor
open scoped BigOperators
namespace ThreeSum.LightTernaryPairedPotential
theorem _root_.solution (m : ℕ) : (program m)[1]?=some powTableBody := rfl
end ThreeSum.LightTernaryPairedPotential
