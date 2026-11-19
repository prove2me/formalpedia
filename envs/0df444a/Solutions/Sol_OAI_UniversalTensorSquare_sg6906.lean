-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg6906
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:13:54.575406+00:00
-- url     : https://prove2.me/submissions/ab70a0ca-5b2a-46b1-afde-ca548e347c4b

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg997
import Theorems.Thm_OAI_UniversalTensorSquare_sg998

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 15. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6906_oai : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg997 sg998

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg6906_oai := @OAI.UniversalTensorSquare.sg6906_oai
