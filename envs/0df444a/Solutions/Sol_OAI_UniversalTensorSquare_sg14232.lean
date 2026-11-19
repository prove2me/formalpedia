-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg14232
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:19:56.131585+00:00
-- url     : https://prove2.me/submissions/29e78ab7-d3b5-4610-ad0f-730cd71a583c

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg2281
import Theorems.Thm_OAI_UniversalTensorSquare_sg2959

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

lemma sg14232_oai : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2281 sg2959

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg14232_oai := @OAI.UniversalTensorSquare.sg14232_oai
