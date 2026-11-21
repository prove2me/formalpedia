-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24067
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:18:04.018205+00:00
-- url     : https://prove2.me/submissions/637a5749-cb4e-48ea-ae5f-870eb3afce2f

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg11439
import Theorems.Thm_OAI_UniversalTensorSquare_sg7240

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 58. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24067_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,5,5,5,5,4,4] := by
  exact rowSquare_join (by decide) sg7240 sg11439

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24067_oai := @OAI.UniversalTensorSquare.sg24067_oai
