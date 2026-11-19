-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg33868
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:30:17.076957+00:00
-- url     : https://prove2.me/submissions/8253b545-8b81-4073-bb6f-07b4ca2f182c

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg19206
import Theorems.Thm_OAI_UniversalTensorSquare_sg19620

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 83. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg33868_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,9,9,5,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19620 sg19206

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg33868_oai := @OAI.UniversalTensorSquare.sg33868_oai
