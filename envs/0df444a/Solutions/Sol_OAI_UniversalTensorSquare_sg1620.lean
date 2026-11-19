-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg1620
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T15:53:58.650726+00:00
-- url     : https://prove2.me/submissions/8adc29e6-84e3-4826-a211-8ae16530a380

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg383

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 2. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1620_oai : RowSquare [4,1,1,1,1,1,1,1,1] [8,4] := by
  exact rowSquare_join (by decide) sg20 sg383

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg1620_oai := @OAI.UniversalTensorSquare.sg1620_oai
