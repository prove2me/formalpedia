-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg1895
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T02:47:09.503102+00:00
-- url     : https://prove2.me/submissions/1d930437-34a7-48af-8eb0-8e68b4b3c0d4

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg180
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

lemma sg1895_oai : RowSquare [7,2,2,1] [3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg180

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg1895_oai := @OAI.UniversalTensorSquare.sg1895_oai
