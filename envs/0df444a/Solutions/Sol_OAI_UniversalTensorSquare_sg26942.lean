-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg26942
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T02:18:30.431222+00:00
-- url     : https://prove2.me/submissions/9218b94f-dbf1-4ace-9bd3-c30887445b5f

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg8721
import Theorems.Thm_OAI_UniversalTensorSquare_sg9578

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 66. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg26942_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,7,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9578

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg26942_oai := @OAI.UniversalTensorSquare.sg26942_oai
