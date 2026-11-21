-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg38612
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T13:18:17.3582+00:00
-- url     : https://prove2.me/submissions/36249dd5-bee9-45c3-a313-8665dc9b7e69

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg18550
import Theorems.Thm_OAI_UniversalTensorSquare_sg20316
import Definitions.Def_OAIQ259US001
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes95
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 95. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg38612_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,4,4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18550

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg38612_oai := @OAI.UniversalTensorSquare.sg38612_oai
