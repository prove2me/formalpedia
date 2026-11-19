-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg20649
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:29:18.909328+00:00
-- url     : https://prove2.me/submissions/30a2105b-d698-4e7f-8a53-6c8e3b5fd422

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg3258
import Theorems.Thm_OAI_UniversalTensorSquare_sg4346

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 50. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20649_oai : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3258 sg4346

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg20649_oai := @OAI.UniversalTensorSquare.sg20649_oai
