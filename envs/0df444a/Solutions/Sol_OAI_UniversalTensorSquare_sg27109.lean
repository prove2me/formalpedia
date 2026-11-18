-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg27109
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T02:21:10.642188+00:00
-- url     : https://prove2.me/submissions/217296a9-8e3f-4f30-bf14-f736c43dcba0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10105
import Theorems.Thm_OAI_UniversalTensorSquare_sg8550

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 66. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg27109_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,4,4,4,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8550 sg10105

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg27109_oai := @OAI.UniversalTensorSquare.sg27109_oai
