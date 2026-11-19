-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg14364
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:18:38.385806+00:00
-- url     : https://prove2.me/submissions/830bfef7-eab9-4033-8baa-1c73557abfd1

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg2297
import Theorems.Thm_OAI_UniversalTensorSquare_sg2895

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 34. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14364_oai : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,5,3] := by
  exact rowSquare_join (by decide) sg2297 sg2895

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg14364_oai := @OAI.UniversalTensorSquare.sg14364_oai
