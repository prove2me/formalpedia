-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg6927
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:16:39.51198+00:00
-- url     : https://prove2.me/submissions/1e237530-04bc-47ed-9e4d-0197aa1340d9

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg1002

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 15. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6927_oai : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1002 sg1001

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg6927_oai := @OAI.UniversalTensorSquare.sg6927_oai
