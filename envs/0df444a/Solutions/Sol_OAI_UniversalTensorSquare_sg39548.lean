-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg39548
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T14:23:13.604772+00:00
-- url     : https://prove2.me/submissions/b1ad54d9-ae1a-4cb9-b3f6-aecb613e9521

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg20316
import Theorems.Thm_OAI_UniversalTensorSquare_sg8057
import Theorems.Thm_OAI_UniversalTensorSquare_sg838
import Definitions.Def_OAIQ259US001
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 45. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg18602 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,8,6,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg838 sg8057

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes97
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 97. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg39548_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,9,5,5,5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18602

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg39548_oai := @OAI.UniversalTensorSquare.sg39548_oai
