-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg12142
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T02:48:43.355992+00:00
-- url     : https://prove2.me/submissions/40d634a4-f00d-41e6-82e2-cc16934e4871
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1202
import Theorems.Thm_OAI_UniversalTensorSquare_sg2050

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 29. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12142_oai : RowSquare [8,6,2,2,2,2,1,1] [7,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg2050

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg12142_oai := @OAI.UniversalTensorSquare.sg12142_oai
