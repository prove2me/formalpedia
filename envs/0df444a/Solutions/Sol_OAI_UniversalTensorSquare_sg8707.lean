-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg8707
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:27:28.712392+00:00
-- url     : https://prove2.me/submissions/5189428c-c97e-483e-9654-aac9593178cd

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1338
import Theorems.Thm_OAI_UniversalTensorSquare_sg889

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 20. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8707_oai : RowSquare [6,6,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg889 sg1338

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg8707_oai := @OAI.UniversalTensorSquare.sg8707_oai
