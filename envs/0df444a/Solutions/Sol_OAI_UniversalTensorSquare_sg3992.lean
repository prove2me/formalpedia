-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg3992
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T14:51:03.022251+00:00
-- url     : https://prove2.me/submissions/5f528b60-c613-4dfa-9bc3-d8d8c5ecff3e

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Definitions.Def_OAIQ259US001
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg74
import Theorems.Thm_OAI_UniversalTensorSquare_sg759
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 8. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3992_oai : RowSquare [5,4,3,2,1,1] [3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg759

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg3992_oai := @OAI.UniversalTensorSquare.sg3992_oai
