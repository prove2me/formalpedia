-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg9473
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:52:38.438084+00:00
-- url     : https://prove2.me/submissions/150e868f-0ced-4879-94a8-0c04b75577f4

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1430

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9473_oai : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1430

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg9473_oai := @OAI.UniversalTensorSquare.sg9473_oai
