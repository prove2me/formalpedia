-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg7718
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:50:10.2152+00:00
-- url     : https://prove2.me/submissions/4380f003-62f8-485d-b457-226d845851e6

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1007
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

lemma sg7718_oai : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,7,4,1,1] := by
  exact rowSquare_join (by decide) sg1007 sg903

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg7718_oai := @OAI.UniversalTensorSquare.sg7718_oai
