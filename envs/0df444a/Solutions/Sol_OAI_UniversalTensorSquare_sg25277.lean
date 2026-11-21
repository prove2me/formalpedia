-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25277
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:47:45.037916+00:00
-- url     : https://prove2.me/submissions/3d3f2e73-1d43-4791-93b6-091bd63b4a38

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1332
import Theorems.Thm_OAI_UniversalTensorSquare_sg1425
import Theorems.Thm_OAI_UniversalTensorSquare_sg8721

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

lemma sg9525 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg1332 sg1425

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

lemma sg25277_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9525

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25277_oai := @OAI.UniversalTensorSquare.sg25277_oai
