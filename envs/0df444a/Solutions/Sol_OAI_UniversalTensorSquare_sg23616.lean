-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23616
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:38:20.092908+00:00
-- url     : https://prove2.me/submissions/1bfa38af-ace1-4883-9646-88bbf74914f9

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg7781
import Theorems.Thm_OAI_UniversalTensorSquare_sg8282

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

lemma sg23616_oai : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg7781 sg8282

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23616_oai := @OAI.UniversalTensorSquare.sg23616_oai
