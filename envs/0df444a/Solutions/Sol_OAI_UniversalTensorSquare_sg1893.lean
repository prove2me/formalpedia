-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg1893
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T02:47:06.867967+00:00
-- url     : https://prove2.me/submissions/d47e837b-9e57-4aca-9527-a00782dcfdc3

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg179
import Theorems.Thm_OAI_UniversalTensorSquare_sg32

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1893_oai : RowSquare [7,2,2,1] [3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg179

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg1893_oai := @OAI.UniversalTensorSquare.sg1893_oai
