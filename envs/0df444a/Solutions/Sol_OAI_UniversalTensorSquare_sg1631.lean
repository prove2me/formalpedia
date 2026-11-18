-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg1631
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:22:47.328809+00:00
-- url     : https://prove2.me/submissions/fadb86fd-d46e-44b7-836c-7b8fe993fd4d

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg334

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

lemma sg1631_oai : RowSquare [4,2,2,2,1,1] [3,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg334

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg1631_oai := @OAI.UniversalTensorSquare.sg1631_oai
