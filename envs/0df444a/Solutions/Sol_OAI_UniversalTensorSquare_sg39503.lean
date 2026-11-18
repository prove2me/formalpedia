-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg39503
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:39:31.245453+00:00
-- url     : https://prove2.me/submissions/b24acbec-2a83-4c77-9c31-716aeee96065
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg16742
import Theorems.Thm_OAI_UniversalTensorSquare_sg20640

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes97
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 97. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg39503_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,8,8,7,6,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20640 sg16742

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg39503_oai := @OAI.UniversalTensorSquare.sg39503_oai
