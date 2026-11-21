-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg4492
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T20:26:23.905199+00:00
-- url     : https://prove2.me/submissions/cbee700e-4959-45ec-9dd6-8c79ae97b916

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Definitions.Def_OAIQ259US001
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1006
import Theorems.Thm_OAI_UniversalTensorSquare_sg74
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 9. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4492_oai : RowSquare [9,3,2,1,1] [4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg1006

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg4492_oai := @OAI.UniversalTensorSquare.sg4492_oai
