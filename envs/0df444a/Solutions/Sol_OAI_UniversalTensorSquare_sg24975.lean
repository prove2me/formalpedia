-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24975
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T06:48:47.407096+00:00
-- url     : https://prove2.me/submissions/c758caab-e6a8-4e14-9c94-5835bbe00cfa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10243
import Theorems.Thm_OAI_UniversalTensorSquare_sg8425

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 61. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24975_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10243

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24975_oai := @OAI.UniversalTensorSquare.sg24975_oai
