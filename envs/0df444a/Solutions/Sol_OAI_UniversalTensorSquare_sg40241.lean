-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg40241
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T15:15:11.649543+00:00
-- url     : https://prove2.me/submissions/b071b085-fc98-4212-9f30-052ef43cd7c5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg15
import Theorems.Thm_OAI_UniversalTensorSquare_sg20316
import Theorems.Thm_OAI_UniversalTensorSquare_sg4966
import Theorems.Thm_OAI_UniversalTensorSquare_sg876
import Definitions.Def_OAIQ259US001

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 33. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14104 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [6,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg876 sg4966

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sg18646 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [10,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg15 sg14104

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes99
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 99. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg40241_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,6,6,6,6,6,6,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18646

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg40241_oai := @OAI.UniversalTensorSquare.sg40241_oai
