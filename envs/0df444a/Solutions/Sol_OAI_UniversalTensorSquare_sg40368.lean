-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg40368
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:39:04.879855+00:00
-- url     : https://prove2.me/submissions/d952a935-41c9-447e-8811-b02882e0409f

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17362
import Theorems.Thm_OAI_UniversalTensorSquare_sg20529

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes99
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 99. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg40368_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,7,7,7,7,7,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20529 sg17362

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg40368_oai := @OAI.UniversalTensorSquare.sg40368_oai
