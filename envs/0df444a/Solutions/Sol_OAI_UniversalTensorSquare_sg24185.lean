-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24185
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:18:08.127129+00:00
-- url     : https://prove2.me/submissions/986ced2f-77e5-42b3-b9e0-418430c8a8d9

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg11439
import Theorems.Thm_OAI_UniversalTensorSquare_sg7243

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 59. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24185_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,5,3,3] := by
  exact rowSquare_join (by decide) sg7243 sg11439

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24185_oai := @OAI.UniversalTensorSquare.sg24185_oai
