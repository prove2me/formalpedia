-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25149
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:44:48.111134+00:00
-- url     : https://prove2.me/submissions/9877b731-96ee-448b-948c-5b6dd6c2ecab

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg1756
import Theorems.Thm_OAI_UniversalTensorSquare_sg8666

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9677 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1001 sg1756

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 61. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25149_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8666 sg9677

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25149_oai := @OAI.UniversalTensorSquare.sg25149_oai
