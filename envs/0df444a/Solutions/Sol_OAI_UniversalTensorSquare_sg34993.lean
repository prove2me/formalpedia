-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg34993
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:24:29.12768+00:00
-- url     : https://prove2.me/submissions/65c44635-9cb0-4e3c-baf9-6552b59b4df2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17337
import Theorems.Thm_OAI_UniversalTensorSquare_sg20512

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 86. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg34993_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,11,8,5,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17337

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg34993_oai := @OAI.UniversalTensorSquare.sg34993_oai
