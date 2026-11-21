-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg34051
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T08:02:59.941401+00:00
-- url     : https://prove2.me/submissions/aec3b4e5-53f6-48c2-81b1-f04ce3b1afec

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17335
import Theorems.Thm_OAI_UniversalTensorSquare_sg20507

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 83. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg34051_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,7,7,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17335

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg34051_oai := @OAI.UniversalTensorSquare.sg34051_oai
