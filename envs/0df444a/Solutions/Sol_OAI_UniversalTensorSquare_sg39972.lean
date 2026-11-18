-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg39972
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:40:20.551746+00:00
-- url     : https://prove2.me/submissions/b80e0da6-0d13-453d-b87b-d5405464b487
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1329
import Theorems.Thm_OAI_UniversalTensorSquare_sg15774
import Theorems.Thm_OAI_UniversalTensorSquare_sg165
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 28. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11751 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg2251

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 50. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20866 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg165 sg11751

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 98. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg39972_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,9,9,8,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20866 sg15774

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg39972_oai := @OAI.UniversalTensorSquare.sg39972_oai
