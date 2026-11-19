-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg5632
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T20:46:10.926195+00:00
-- url     : https://prove2.me/submissions/a946d6c4-b061-4458-8f01-7c83f0ea3367

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg377
import Theorems.Thm_OAI_UniversalTensorSquare_sg903
import Definitions.Def_OAIQ259US001
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

lemma sg5632_oai : RowSquare [6,4,1,1,1,1,1,1,1,1] [7,7,3,1] := by
  exact rowSquare_join (by decide) sg377 sg903

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg5632_oai := @OAI.UniversalTensorSquare.sg5632_oai
