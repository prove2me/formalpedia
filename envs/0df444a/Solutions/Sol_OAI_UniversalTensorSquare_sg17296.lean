-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg17296
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:31:46.84326+00:00
-- url     : https://prove2.me/submissions/4920c229-4152-4097-be2f-9c16ca7b5724
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg3329
import Theorems.Thm_OAI_UniversalTensorSquare_sg4467

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 41. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg17296_oai : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,3,3,3,2] := by
  exact rowSquare_join (by decide) sg3329 sg4467

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg17296_oai := @OAI.UniversalTensorSquare.sg17296_oai
