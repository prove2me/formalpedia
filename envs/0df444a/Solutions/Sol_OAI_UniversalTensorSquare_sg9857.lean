-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg9857
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:16:57.364537+00:00
-- url     : https://prove2.me/submissions/cd9d02d5-6ff1-4258-adf9-cdd11d1d5105

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1330
import Theorems.Thm_OAI_UniversalTensorSquare_sg1388
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 23. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9857_oai : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1388

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg9857_oai := @OAI.UniversalTensorSquare.sg9857_oai
