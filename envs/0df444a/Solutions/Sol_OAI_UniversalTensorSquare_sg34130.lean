-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg34130
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T08:07:56.966755+00:00
-- url     : https://prove2.me/submissions/af9bd6db-5a0f-4342-bdf8-fa69bcbe0ec4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg20509
import Theorems.Thm_OAI_UniversalTensorSquare_sg2318
import Theorems.Thm_OAI_UniversalTensorSquare_sg3004

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 32. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg13731 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,3,3] := by
  exact rowSquare_join (by decide) sg2318 sg3004

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 41. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg17307 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13731

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 83. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg34130_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,8,5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20509 sg17307

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg34130_oai := @OAI.UniversalTensorSquare.sg34130_oai
