-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23766
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T18:03:20.108203+00:00
-- url     : https://prove2.me/submissions/c9486b34-0aa4-483e-8d67-7fec4b30a1c4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg23672

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

lemma sg23766_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,5,5,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg23672

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23766_oai := @OAI.UniversalTensorSquare.sg23766_oai
