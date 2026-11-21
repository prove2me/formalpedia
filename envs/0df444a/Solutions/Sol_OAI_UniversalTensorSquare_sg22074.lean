-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg22074
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:02:58.561654+00:00
-- url     : https://prove2.me/submissions/a58e6317-449b-4040-b094-7b4b184261fc

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg6409
import Theorems.Thm_OAI_UniversalTensorSquare_sg6823

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 53. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg22074_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,6,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6409 sg6823

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg22074_oai := @OAI.UniversalTensorSquare.sg22074_oai
