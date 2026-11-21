-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg22899
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T06:54:45.033544+00:00
-- url     : https://prove2.me/submissions/6cf743d7-c892-4f0b-b1b5-13a52da0dc3f

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg151
import Theorems.Thm_OAI_UniversalTensorSquare_sg21071

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 55. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg22899_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg151 sg21071

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg22899_oai := @OAI.UniversalTensorSquare.sg22899_oai
