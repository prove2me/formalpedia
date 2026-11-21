-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24387
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T00:32:10.741602+00:00
-- url     : https://prove2.me/submissions/15160262-6c80-4760-aaf2-e65291ce6e6c

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg12619
import Theorems.Thm_OAI_UniversalTensorSquare_sg314

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

lemma sg5550 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg314 sg1001

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 59. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24387_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,3,3,3] := by
  exact rowSquare_join (by decide) sg5550 sg12619

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24387_oai := @OAI.UniversalTensorSquare.sg24387_oai
