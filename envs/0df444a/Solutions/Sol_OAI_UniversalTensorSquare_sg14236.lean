-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg14236
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:39:54.386425+00:00
-- url     : https://prove2.me/submissions/0a874f0b-1ea7-452c-9ac5-53781539c992

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg4987

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 34. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14236_oai : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1001 sg4987

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg14236_oai := @OAI.UniversalTensorSquare.sg14236_oai
