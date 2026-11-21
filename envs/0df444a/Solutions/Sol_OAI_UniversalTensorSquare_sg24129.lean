-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24129
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:17:54.09027+00:00
-- url     : https://prove2.me/submissions/c64accde-cfd4-40c1-8cdb-14921b709e97

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg12619
import Theorems.Thm_OAI_UniversalTensorSquare_sg314
import Theorems.Thm_OAI_UniversalTensorSquare_sg998

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 12. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5540 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg314 sg998

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 58. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24129_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,5,5,4,4,4] := by
  exact rowSquare_join (by decide) sg5540 sg12619

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24129_oai := @OAI.UniversalTensorSquare.sg24129_oai
