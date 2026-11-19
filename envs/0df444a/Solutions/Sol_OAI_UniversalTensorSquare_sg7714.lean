-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg7714
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:49:47.451188+00:00
-- url     : https://prove2.me/submissions/081a41e5-e6c6-4e19-b9b3-37ca7bd1c74f

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg909
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

lemma sg7714_oai : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,7,2,2,2] := by
  exact rowSquare_join (by decide) sg1001 sg909

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg7714_oai := @OAI.UniversalTensorSquare.sg7714_oai
