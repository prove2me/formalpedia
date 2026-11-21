-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg33180
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T04:53:23.239752+00:00
-- url     : https://prove2.me/submissions/97c4d9a1-6b7b-43e7-bd0f-5a55126ba6a4

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg18141
import Theorems.Thm_OAI_UniversalTensorSquare_sg20423

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

lemma sg33180_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20423 sg18141

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg33180_oai := @OAI.UniversalTensorSquare.sg33180_oai
