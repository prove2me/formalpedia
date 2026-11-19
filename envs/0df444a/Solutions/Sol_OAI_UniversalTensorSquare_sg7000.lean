-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg7000
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:18:11.378903+00:00
-- url     : https://prove2.me/submissions/b9db74a1-fa08-4865-ac9f-33bea47a18cc

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg1015

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

lemma sg7000_oai : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,6,3,3,2] := by
  exact rowSquare_join (by decide) sg1001 sg1015

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg7000_oai := @OAI.UniversalTensorSquare.sg7000_oai
