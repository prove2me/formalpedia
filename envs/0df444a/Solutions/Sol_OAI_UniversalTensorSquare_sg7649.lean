-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg7649
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:45:36.239195+00:00
-- url     : https://prove2.me/submissions/c410c53f-b8d7-4869-942c-8461c59abdf1

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg903
import Theorems.Thm_OAI_UniversalTensorSquare_sg998
import Definitions.Def_OAIQ259US001
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 17. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7649_oai : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg903

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg7649_oai := @OAI.UniversalTensorSquare.sg7649_oai
