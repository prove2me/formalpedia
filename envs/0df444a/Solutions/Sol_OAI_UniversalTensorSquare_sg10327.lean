-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg10327
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:08:58.843994+00:00
-- url     : https://prove2.me/submissions/e07e7d08-7a21-41c9-827e-01e5c256f5f2

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg6922

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10327_oai : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6922

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg10327_oai := @OAI.UniversalTensorSquare.sg10327_oai
