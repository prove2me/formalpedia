-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg7657
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:46:27.033024+00:00
-- url     : https://prove2.me/submissions/9814ca07-f295-4b44-a6d8-c3262ac6fa8f

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1007
import Theorems.Thm_OAI_UniversalTensorSquare_sg899
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

lemma sg7657_oai : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,6,4,3,1] := by
  exact rowSquare_join (by decide) sg1007 sg899

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg7657_oai := @OAI.UniversalTensorSquare.sg7657_oai
