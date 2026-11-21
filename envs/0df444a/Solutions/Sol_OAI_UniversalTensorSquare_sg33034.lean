-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg33034
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T04:14:38.113361+00:00
-- url     : https://prove2.me/submissions/7ea0a212-cb5e-4cd4-8007-3d5e81d78f5c

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg16266
import Theorems.Thm_OAI_UniversalTensorSquare_sg20712

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 81. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg33034_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20712 sg16266

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg33034_oai := @OAI.UniversalTensorSquare.sg33034_oai
