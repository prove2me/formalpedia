-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg3329
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T03:56:29.084409+00:00
-- url     : https://prove2.me/submissions/5174362a-cc15-4c08-99c5-683e0d5e2e5b

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg442
import Theorems.Thm_OAI_UniversalTensorSquare_sg89

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

lemma sg3329_oai : RowSquare [6,3,3,1,1,1] [3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg89 sg442

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg3329_oai := @OAI.UniversalTensorSquare.sg3329_oai
