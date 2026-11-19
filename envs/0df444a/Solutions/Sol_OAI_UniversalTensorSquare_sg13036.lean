-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg13036
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T07:57:08.04097+00:00
-- url     : https://prove2.me/submissions/bcc0f3a8-64f9-4358-b1a2-dcdd8248a84a

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1637
import Theorems.Thm_OAI_UniversalTensorSquare_sg2547

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 31. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg13036_oai : RowSquare [8,7,2,2,2,2,2,1] [7,4,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1637 sg2547

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg13036_oai := @OAI.UniversalTensorSquare.sg13036_oai
