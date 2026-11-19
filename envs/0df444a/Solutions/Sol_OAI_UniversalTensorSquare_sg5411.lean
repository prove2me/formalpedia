-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg5411
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T20:41:35.048103+00:00
-- url     : https://prove2.me/submissions/46145b43-8294-4db6-9880-541e43b14b3b

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg383
import Theorems.Thm_OAI_UniversalTensorSquare_sg998

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 12. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5411_oai : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [6,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg383 sg998

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg5411_oai := @OAI.UniversalTensorSquare.sg5411_oai
