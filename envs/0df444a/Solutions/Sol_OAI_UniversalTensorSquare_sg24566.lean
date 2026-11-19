-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24566
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:28:47.155572+00:00
-- url     : https://prove2.me/submissions/f9f5426c-71e6-4240-ac49-e58a12ac3ab9

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10108
import Theorems.Thm_OAI_UniversalTensorSquare_sg8525

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 60. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24566_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8525 sg10108

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24566_oai := @OAI.UniversalTensorSquare.sg24566_oai
