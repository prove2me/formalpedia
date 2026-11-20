-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23390
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T15:35:33.177613+00:00
-- url     : https://prove2.me/submissions/25aed8f0-816e-4593-ac0c-100816c1f7a7

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg14308
import Theorems.Thm_OAI_UniversalTensorSquare_sg1814

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 57. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23390_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1814 sg14308

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23390_oai := @OAI.UniversalTensorSquare.sg23390_oai
