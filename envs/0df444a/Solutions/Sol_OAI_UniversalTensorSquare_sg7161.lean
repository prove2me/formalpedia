-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg7161
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:25:14.756178+00:00
-- url     : https://prove2.me/submissions/dfc46b8c-2264-4a7a-8e34-c192354034ef

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg932
import Theorems.Thm_OAI_UniversalTensorSquare_sg998

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7161_oai : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg932

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg7161_oai := @OAI.UniversalTensorSquare.sg7161_oai
