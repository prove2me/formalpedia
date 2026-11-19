-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg11736
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T10:11:35.352764+00:00
-- url     : https://prove2.me/submissions/a1194ef9-e957-4a37-ad3d-22cd1dd0fbe5

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg2633

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 27. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11736_oai : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1001 sg2633

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg11736_oai := @OAI.UniversalTensorSquare.sg11736_oai
