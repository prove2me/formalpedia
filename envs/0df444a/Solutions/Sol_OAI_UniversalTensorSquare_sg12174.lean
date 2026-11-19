-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg12174
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T02:48:54.449057+00:00
-- url     : https://prove2.me/submissions/f3bd3bae-ffda-434d-9de9-952ecf0d16d0

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1202
import Theorems.Thm_OAI_UniversalTensorSquare_sg2058

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 29. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12174_oai : RowSquare [8,6,2,2,2,2,1,1] [7,6,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg2058

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg12174_oai := @OAI.UniversalTensorSquare.sg12174_oai
