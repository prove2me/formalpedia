-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25873
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T08:57:21.489521+00:00
-- url     : https://prove2.me/submissions/f2fc758c-8663-417b-8f87-d0674ba3dd2f

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10283
import Theorems.Thm_OAI_UniversalTensorSquare_sg8423

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 63. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25873_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10283

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25873_oai := @OAI.UniversalTensorSquare.sg25873_oai
