-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg9748
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:07:04.746803+00:00
-- url     : https://prove2.me/submissions/daeeaa6a-339e-4fcc-a5c8-e0ee8c61b8b7

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1332
import Theorems.Thm_OAI_UniversalTensorSquare_sg1377
import Definitions.Def_OAIQ259US001

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

lemma sg9748_oai : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg1332 sg1377

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg9748_oai := @OAI.UniversalTensorSquare.sg9748_oai
