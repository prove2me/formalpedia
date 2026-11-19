-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25736
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:56:22.043509+00:00
-- url     : https://prove2.me/submissions/686673a5-208e-4e19-ba31-f9d00b95915d

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10130
import Theorems.Thm_OAI_UniversalTensorSquare_sg8525

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25736_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8525 sg10130

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25736_oai := @OAI.UniversalTensorSquare.sg25736_oai
