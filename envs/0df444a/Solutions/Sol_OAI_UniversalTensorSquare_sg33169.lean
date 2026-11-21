-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg33169
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T04:51:49.066986+00:00
-- url     : https://prove2.me/submissions/2976990f-7099-4503-93a4-14c9f137ca48

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17268
import Theorems.Thm_OAI_UniversalTensorSquare_sg20511

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

lemma sg33169_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20511 sg17268

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg33169_oai := @OAI.UniversalTensorSquare.sg33169_oai
