-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg2636
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T02:08:18.734572+00:00
-- url     : https://prove2.me/submissions/b0260ba0-73e8-4fcd-ba44-5da81fd34cb3

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg241
import Theorems.Thm_OAI_UniversalTensorSquare_sg91

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2636_oai : RowSquare [6,3,2,1,1,1] [3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg91 sg241

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg2636_oai := @OAI.UniversalTensorSquare.sg2636_oai
