-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg9140
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:39:13.722792+00:00
-- url     : https://prove2.me/submissions/773cbba1-958c-40b3-9b7b-104e1935cfe9

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg8167

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 21. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9140_oai : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,5,5,1] := by
  exact rowSquare_join (by decide) sg0 sg8167

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg9140_oai := @OAI.UniversalTensorSquare.sg9140_oai
