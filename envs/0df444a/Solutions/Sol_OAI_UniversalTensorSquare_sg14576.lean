-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg14576
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T14:06:41.047411+00:00
-- url     : https://prove2.me/submissions/a4d9fd0d-aff0-41c8-a3a7-bba0938c7594

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg306
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg3709

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 4. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2212 : RowSquare [6,4,3] [2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg306

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14576_oai : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2212 sg3709

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg14576_oai := @OAI.UniversalTensorSquare.sg14576_oai
