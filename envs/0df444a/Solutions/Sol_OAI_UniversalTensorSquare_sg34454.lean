-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg34454
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T04:16:12.65042+00:00
-- url     : https://prove2.me/submissions/d24240a0-e11c-426f-aa4b-e5365a1fb2dd

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17310
import Theorems.Thm_OAI_UniversalTensorSquare_sg20525
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 84. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg34454_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,9,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20525 sg17310

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg34454_oai := @OAI.UniversalTensorSquare.sg34454_oai
