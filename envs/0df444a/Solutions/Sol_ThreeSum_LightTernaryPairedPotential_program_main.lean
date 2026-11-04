-- Prove2me | solution 1 for ThreeSum.LightTernaryPairedPotential.program_main
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:50:54.604957+00:00
-- url     : https://prove2.me/submissions/3e5a1613-d610-4740-9597-806ba7cab5f0

import Definitions.Def_Submission_ThreeSum_TernaryPairedColumnEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPotential
open Light LightTernaryPairedPolynomial TernaryPairedColumnEnumeration TernaryPairedTensor
open scoped BigOperators
namespace ThreeSum.LightTernaryPairedPotential
theorem _root_.solution (m : ℕ) : (program m)[0]?=some (body m 1 2 5) := rfl
end ThreeSum.LightTernaryPairedPotential
