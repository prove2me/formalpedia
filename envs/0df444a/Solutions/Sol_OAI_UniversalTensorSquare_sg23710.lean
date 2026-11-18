-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23710
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:14:10.874397+00:00
-- url     : https://prove2.me/submissions/4027b929-bf3f-4710-970d-eb2f135ffc9f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg8648
import Theorems.Thm_OAI_UniversalTensorSquare_sg9686

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 57. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23710_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,4,4,4,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg8648 sg9686

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23710_oai := @OAI.UniversalTensorSquare.sg23710_oai
