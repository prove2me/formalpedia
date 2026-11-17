-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24865
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T06:35:07.912368+00:00
-- url     : https://prove2.me/submissions/fced0069-369c-4f6a-b091-6d1f35bd531e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1379
import Theorems.Thm_OAI_UniversalTensorSquare_sg8660

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9674 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1379

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 60. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24865_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8660 sg9674

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24865_oai := @OAI.UniversalTensorSquare.sg24865_oai
