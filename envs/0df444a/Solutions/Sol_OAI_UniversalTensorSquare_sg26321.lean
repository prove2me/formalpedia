-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg26321
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T10:09:40.27211+00:00
-- url     : https://prove2.me/submissions/3e217d93-6946-41c1-a724-e77c2e476e8c

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg15535
import Theorems.Thm_OAI_UniversalTensorSquare_sg2224

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 64. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg26321_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2224 sg15535

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg26321_oai := @OAI.UniversalTensorSquare.sg26321_oai
