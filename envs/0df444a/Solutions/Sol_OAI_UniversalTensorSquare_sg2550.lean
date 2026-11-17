-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg2550
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T07:57:22.88604+00:00
-- url     : https://prove2.me/submissions/791425e4-3160-4538-968f-68ec3164c84a

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg179

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

lemma sg2550_oai : RowSquare [4,4,1,1,1,1,1,1] [4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg179 sg179

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg2550_oai := @OAI.UniversalTensorSquare.sg2550_oai
