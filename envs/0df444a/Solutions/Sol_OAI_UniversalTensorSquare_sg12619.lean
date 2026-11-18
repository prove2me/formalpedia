-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg12619
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:48:27.768139+00:00
-- url     : https://prove2.me/submissions/94e0d104-526b-4e5d-94aa-9d44c0109a76
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg4167
import Theorems.Thm_OAI_UniversalTensorSquare_sg587

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 30. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12619_oai : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg587 sg4167

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg12619_oai := @OAI.UniversalTensorSquare.sg12619_oai
