-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg9319
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:47:53.620985+00:00
-- url     : https://prove2.me/submissions/aa74bbea-cd13-4de5-895f-56b8e3b54955

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Definitions.Def_OAIQ259US001
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg4
import Theorems.Thm_OAI_UniversalTensorSquare_sg543
import Theorems.Thm_OAI_UniversalTensorSquare_sg999
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1789 : RowSquare [6,3,1,1,1] [4,4,4] := by
  exact rowSquare_join (by decide) sg4 sg543

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 21. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9319_oai : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1789

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg9319_oai := @OAI.UniversalTensorSquare.sg9319_oai
