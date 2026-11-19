-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg12931
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:39:16.235666+00:00
-- url     : https://prove2.me/submissions/c94f25a1-6185-439a-8041-c75138b94d72

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg4165
import Theorems.Thm_OAI_UniversalTensorSquare_sg892

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 30. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12931_oai : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg892 sg4165

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg12931_oai := @OAI.UniversalTensorSquare.sg12931_oai
