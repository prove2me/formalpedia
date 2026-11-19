-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg3554
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T05:05:34.883205+00:00
-- url     : https://prove2.me/submissions/dee963ae-af36-496d-9ca1-cca26947ae33

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg890

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 7. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3554_oai : RowSquare [8,2,2,1,1,1] [3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg890

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg3554_oai := @OAI.UniversalTensorSquare.sg3554_oai
