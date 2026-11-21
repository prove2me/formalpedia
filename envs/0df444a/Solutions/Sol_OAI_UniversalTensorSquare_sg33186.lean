-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg33186
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T04:53:45.229048+00:00
-- url     : https://prove2.me/submissions/a08a383f-004e-4374-bec6-8449533b8c86

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg16253
import Theorems.Thm_OAI_UniversalTensorSquare_sg20716

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 81. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg33186_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20716 sg16253

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg33186_oai := @OAI.UniversalTensorSquare.sg33186_oai
