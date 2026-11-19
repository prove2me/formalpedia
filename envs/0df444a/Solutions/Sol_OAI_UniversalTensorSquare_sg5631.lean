-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg5631
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T20:46:05.396413+00:00
-- url     : https://prove2.me/submissions/ecb3485f-fea5-4b4b-bcbb-20e5d9c11afa

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg909
import Definitions.Def_OAIQ259US001
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 12. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5631_oai : RowSquare [6,4,1,1,1,1,1,1,1,1] [7,7,2,2] := by
  exact rowSquare_join (by decide) sg373 sg909

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg5631_oai := @OAI.UniversalTensorSquare.sg5631_oai
