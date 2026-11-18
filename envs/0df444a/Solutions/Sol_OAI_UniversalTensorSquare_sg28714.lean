-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg28714
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T02:35:07.16401+00:00
-- url     : https://prove2.me/submissions/75f7de1b-f922-4465-99ec-ea98de06c1db
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg2277
import Theorems.Thm_OAI_UniversalTensorSquare_sg7454
import Theorems.Thm_OAI_UniversalTensorSquare_sg889

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11333 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg889 sg2277

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 70. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg28714_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,5,4,4,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7454 sg11333

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg28714_oai := @OAI.UniversalTensorSquare.sg28714_oai
