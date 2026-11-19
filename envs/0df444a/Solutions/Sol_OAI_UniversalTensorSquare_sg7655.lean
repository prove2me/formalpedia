-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg7655
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:46:15.448552+00:00
-- url     : https://prove2.me/submissions/f9c6005c-ffe8-40d3-b9d3-dc1cca36158f

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1000
import Theorems.Thm_OAI_UniversalTensorSquare_sg903
import Definitions.Def_OAIQ259US001
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 17. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7655_oai : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,6,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg903

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg7655_oai := @OAI.UniversalTensorSquare.sg7655_oai
