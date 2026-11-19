-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg1349
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:41:46.15877+00:00
-- url     : https://prove2.me/submissions/c2c7382a-39c2-4607-bf9a-b15b635d49c2

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg899

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 2. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1349_oai : RowSquare [6,1,1,1,1,1] [4,4,2,1] := by
  exact rowSquare_join (by decide) sg0 sg899

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg1349_oai := @OAI.UniversalTensorSquare.sg1349_oai
