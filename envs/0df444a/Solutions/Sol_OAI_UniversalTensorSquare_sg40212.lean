-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg40212
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:31:25.66709+00:00
-- url     : https://prove2.me/submissions/adcd66a7-ac81-4432-af01-eebcb6392211

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg16317
import Theorems.Thm_OAI_UniversalTensorSquare_sg20728

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

lemma sg40212_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,12,7,7,7,5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20728 sg16317

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg40212_oai := @OAI.UniversalTensorSquare.sg40212_oai
