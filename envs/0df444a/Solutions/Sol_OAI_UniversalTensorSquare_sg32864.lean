-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg32864
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T03:55:44.41267+00:00
-- url     : https://prove2.me/submissions/60308696-4e89-4c75-b080-ec888ebe44f8

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg16237
import Theorems.Thm_OAI_UniversalTensorSquare_sg20712

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 80. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg32864_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,8,8,8,7,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20712 sg16237

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg32864_oai := @OAI.UniversalTensorSquare.sg32864_oai
