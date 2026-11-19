-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg6192
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T20:57:10.779193+00:00
-- url     : https://prove2.me/submissions/bd6655b9-3187-4d1e-840c-3c2d93a536de

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg588
import Theorems.Thm_OAI_UniversalTensorSquare_sg999

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6192_oai : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg588 sg999

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg6192_oai := @OAI.UniversalTensorSquare.sg6192_oai
