-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg33773
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T04:04:42.064426+00:00
-- url     : https://prove2.me/submissions/49b9b4e3-5103-49f1-913d-1912180da0a8

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg18917
import Theorems.Thm_OAI_UniversalTensorSquare_sg19640
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 83. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg33773_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,9,8,8,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18917 sg19640

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg33773_oai := @OAI.UniversalTensorSquare.sg33773_oai
