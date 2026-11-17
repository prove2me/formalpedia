-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg29051
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T15:40:24.287196+00:00
-- url     : https://prove2.me/submissions/3aedc6c8-9966-4df6-beb8-aae202a34500
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10280
import Theorems.Thm_OAI_UniversalTensorSquare_sg8434

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 71. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg29051_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,5,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8434 sg10280

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg29051_oai := @OAI.UniversalTensorSquare.sg29051_oai
