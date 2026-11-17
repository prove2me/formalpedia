-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg2552
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T08:04:25.892123+00:00
-- url     : https://prove2.me/submissions/498dc8a1-d4a9-4bcc-8233-b57b171b329b

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg179
import Theorems.Thm_OAI_UniversalTensorSquare_sg181

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2552_oai : RowSquare [4,4,1,1,1,1,1,1] [4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg179 sg181

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg2552_oai := @OAI.UniversalTensorSquare.sg2552_oai
