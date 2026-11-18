-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24069
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:17:28.020406+00:00
-- url     : https://prove2.me/submissions/34546c49-539f-4aea-baf1-a369b5be4854
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1329
import Theorems.Thm_OAI_UniversalTensorSquare_sg2633
import Theorems.Thm_OAI_UniversalTensorSquare_sg312
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
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 23. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10086 : RowSquare [6,5,3,2,1,1,1,1,1,1] [4,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg312 sg2633

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

lemma sg24069_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,5,5,5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg8543 sg10086

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24069_oai := @OAI.UniversalTensorSquare.sg24069_oai
