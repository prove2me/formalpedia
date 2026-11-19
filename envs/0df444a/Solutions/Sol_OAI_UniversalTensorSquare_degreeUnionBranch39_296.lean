-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_296
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:04:42.322829+00:00
-- url     : https://prove2.me/submissions/def56e41-928e-4a30-8904-28e6c8b3a12e

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 39. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_296_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 12 27 degreeUnionState39_296 [27] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_296_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_296_oai
