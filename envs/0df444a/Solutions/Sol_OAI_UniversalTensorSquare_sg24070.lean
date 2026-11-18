-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24070
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:17:32.167514+00:00
-- url     : https://prove2.me/submissions/abd3313c-b3f4-4940-83d4-465bf25975a1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg2633
import Theorems.Thm_OAI_UniversalTensorSquare_sg6401
import Theorems.Thm_OAI_UniversalTensorSquare_sg998

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 27. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11735 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg998 sg2633

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

lemma sg24070_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,5,5,5,5,5,3] := by
  exact rowSquare_join (by decide) sg6401 sg11735

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24070_oai := @OAI.UniversalTensorSquare.sg24070_oai
