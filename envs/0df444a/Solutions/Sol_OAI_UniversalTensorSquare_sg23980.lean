-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23980
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T04:16:19.297005+00:00
-- url     : https://prove2.me/submissions/bf74d2be-f6bd-467d-9ef9-241188a3aef4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10601
import Theorems.Thm_OAI_UniversalTensorSquare_sg8365

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 58. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23980_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,6,6,6,5,3,3] := by
  exact rowSquare_join (by decide) sg8365 sg10601

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23980_oai := @OAI.UniversalTensorSquare.sg23980_oai
