-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg35636
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T11:48:10.984212+00:00
-- url     : https://prove2.me/submissions/19c1a329-8352-4015-be55-e08068cfc6fb

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17216
import Theorems.Thm_OAI_UniversalTensorSquare_sg20529

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 87. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg35636_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,7,7,7,7,6,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20529 sg17216

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg35636_oai := @OAI.UniversalTensorSquare.sg35636_oai
