-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg17310
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T11:39:56.579201+00:00
-- url     : https://prove2.me/submissions/15b81942-8aee-455b-9cec-6ceac5892395

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg3556
import Theorems.Thm_OAI_UniversalTensorSquare_sg4309

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 41. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg17310_oai : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,5,1] := by
  exact rowSquare_join (by decide) sg3556 sg4309

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg17310_oai := @OAI.UniversalTensorSquare.sg17310_oai
