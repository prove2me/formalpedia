-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25611
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:53:49.612889+00:00
-- url     : https://prove2.me/submissions/29af8420-11f8-47a2-8734-23c2446a17fe

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10658
import Theorems.Thm_OAI_UniversalTensorSquare_sg8350

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25611_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg8350 sg10658

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25611_oai := @OAI.UniversalTensorSquare.sg25611_oai
