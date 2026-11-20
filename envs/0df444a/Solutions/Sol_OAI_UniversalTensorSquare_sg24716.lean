-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24716
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:34:27.607283+00:00
-- url     : https://prove2.me/submissions/3826634e-f665-4127-8b54-766ccc96096c

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg8721
import Theorems.Thm_OAI_UniversalTensorSquare_sg9507

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 60. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24716_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9507

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24716_oai := @OAI.UniversalTensorSquare.sg24716_oai
