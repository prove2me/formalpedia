-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25743
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:56:30.925803+00:00
-- url     : https://prove2.me/submissions/b5aff5cd-c889-49f3-9570-4df56f3385fe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10100
import Theorems.Thm_OAI_UniversalTensorSquare_sg1329
import Theorems.Thm_OAI_UniversalTensorSquare_sg998

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 20. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8543 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg998 sg1329

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 63. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25743_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg8543 sg10100

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25743_oai := @OAI.UniversalTensorSquare.sg25743_oai
