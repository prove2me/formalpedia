-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg3707
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T14:08:20.02014+00:00
-- url     : https://prove2.me/submissions/e61abaeb-b4a8-4c98-85e3-76509e260074

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg180
import Theorems.Thm_OAI_UniversalTensorSquare_sg371

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 7. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3707_oai : RowSquare [9,2,2,2] [4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg180 sg371

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg3707_oai := @OAI.UniversalTensorSquare.sg3707_oai
