-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg5412
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T20:41:40.525875+00:00
-- url     : https://prove2.me/submissions/b1f9da6d-8d36-4bc0-adf9-fe45d2ed9339

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg383

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 12. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5412_oai : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [6,6,2,2,2] := by
  exact rowSquare_join (by decide) sg383 sg1001

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg5412_oai := @OAI.UniversalTensorSquare.sg5412_oai
