-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg6907
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:14:00.02532+00:00
-- url     : https://prove2.me/submissions/f38597aa-8190-46b0-a8aa-a7200d2fb07d

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg997
import Theorems.Thm_OAI_UniversalTensorSquare_sg999

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

lemma sg6907_oai : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg997 sg999

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg6907_oai := @OAI.UniversalTensorSquare.sg6907_oai
