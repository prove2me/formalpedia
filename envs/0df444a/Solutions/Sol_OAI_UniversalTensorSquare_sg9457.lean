-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg9457
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:52:16.461194+00:00
-- url     : https://prove2.me/submissions/e969871c-c97a-49fb-908f-5b9fe7533cbf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1425

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9457_oai : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1425

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg9457_oai := @OAI.UniversalTensorSquare.sg9457_oai
