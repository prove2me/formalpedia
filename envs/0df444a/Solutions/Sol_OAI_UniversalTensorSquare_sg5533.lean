-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg5533
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T20:45:26.960113+00:00
-- url     : https://prove2.me/submissions/8561d09b-5119-45c8-9cc6-ad1b2fa6ea1f

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg312
import Theorems.Thm_OAI_UniversalTensorSquare_sg999

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

lemma sg5533_oai : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg312 sg999

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg5533_oai := @OAI.UniversalTensorSquare.sg5533_oai
