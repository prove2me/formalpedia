-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg12828
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:17:43.006094+00:00
-- url     : https://prove2.me/submissions/b7b86b4b-c403-4787-bd6f-657a1d5f03b2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg180
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg371
import Theorems.Thm_OAI_UniversalTensorSquare_sg74

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

lemma sg2317 : RowSquare [7,3,2,1] [3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg180

lemma sg2392 : RowSquare [8,2,2,1] [3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg371

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 30. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12828_oai : RowSquare [4,4,3,3,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,2] := by
  exact rowSquare_join (by decide) sg2392 sg2317

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg12828_oai := @OAI.UniversalTensorSquare.sg12828_oai
