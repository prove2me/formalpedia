-- Prove2me | solution 1 for ThreeSum.LightTernaryPairedPotential.program_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:51:43.322973+00:00
-- url     : https://prove2.me/submissions/b099ab0a-3658-440c-a913-35a8edaac669

import Definitions.Def_Submission_ThreeSum_TernaryPairedColumnEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPotential
open Light LightTernaryPairedPolynomial TernaryPairedColumnEnumeration TernaryPairedTensor
open scoped BigOperators
namespace ThreeSum.LightTernaryPairedPotential
theorem _root_.solution (m : ℕ) : (program m)[5]?=some (LightTernaryPairedPolynomial.body m) := rfl
end ThreeSum.LightTernaryPairedPotential
