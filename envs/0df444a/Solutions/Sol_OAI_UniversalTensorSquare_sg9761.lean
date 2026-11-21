-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg9761
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:07:45.220203+00:00
-- url     : https://prove2.me/submissions/1435d630-6826-4896-aa8a-24f2ba071e9a

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg1767
import Definitions.Def_OAIQ259US001

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 23. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9761_oai : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,3] := by
  exact rowSquare_join (by decide) sg1001 sg1767

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg9761_oai := @OAI.UniversalTensorSquare.sg9761_oai
