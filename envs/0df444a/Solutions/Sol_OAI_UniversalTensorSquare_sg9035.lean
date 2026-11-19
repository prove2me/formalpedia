-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg9035
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:37:26.918042+00:00
-- url     : https://prove2.me/submissions/f39f8b29-88ad-4700-98d1-e6ffc5c908bc

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg8126

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

lemma sg9035_oai : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8126

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg9035_oai := @OAI.UniversalTensorSquare.sg9035_oai
