-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg38193
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T20:25:19.862591+00:00
-- url     : https://prove2.me/submissions/244ca704-3311-4fbb-949b-b6ece69b23d8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg18306
import Theorems.Thm_OAI_UniversalTensorSquare_sg3523
import Theorems.Thm_OAI_UniversalTensorSquare_sg4165

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 49. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20321 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3523 sg4165

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes94
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 94. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg38193_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,8,7,7,7,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20321 sg18306

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg38193_oai := @OAI.UniversalTensorSquare.sg38193_oai
