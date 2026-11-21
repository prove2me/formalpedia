-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg15129
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T06:24:16.794116+00:00
-- url     : https://prove2.me/submissions/a75d370e-429f-4231-a047-91760728b017

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg2274
import Theorems.Thm_OAI_UniversalTensorSquare_sg4379

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 36. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg15129_oai : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg2274 sg4379

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg15129_oai := @OAI.UniversalTensorSquare.sg15129_oai
