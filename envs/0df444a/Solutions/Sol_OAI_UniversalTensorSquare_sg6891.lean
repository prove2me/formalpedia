-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg6891
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:13:42.689977+00:00
-- url     : https://prove2.me/submissions/c17f3787-1f92-44d9-ab32-9accc080ba73

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1682
import Theorems.Thm_OAI_UniversalTensorSquare_sg377

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 15. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6891_oai : RowSquare [5,4,3,2,1,1,1,1,1,1] [4,4,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg377 sg1682

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg6891_oai := @OAI.UniversalTensorSquare.sg6891_oai
