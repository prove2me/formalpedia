-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg2055
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:51:56.674316+00:00
-- url     : https://prove2.me/submissions/2555b77b-9048-4116-aa7c-a653ddf0508a

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg180
import Theorems.Thm_OAI_UniversalTensorSquare_sg88

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2055_oai : RowSquare [4,3,1,1,1,1,1,1] [4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg88 sg180

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg2055_oai := @OAI.UniversalTensorSquare.sg2055_oai
