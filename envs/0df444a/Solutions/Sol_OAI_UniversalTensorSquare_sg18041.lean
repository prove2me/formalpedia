-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg18041
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T11:40:00.719209+00:00
-- url     : https://prove2.me/submissions/3e06ed0e-d885-4d66-b968-a28ebd0849ee

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg3556
import Theorems.Thm_OAI_UniversalTensorSquare_sg4187

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 43. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg18041_oai : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,5,5,1] := by
  exact rowSquare_join (by decide) sg3556 sg4187

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg18041_oai := @OAI.UniversalTensorSquare.sg18041_oai
