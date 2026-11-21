-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg4426
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T20:25:45.794777+00:00
-- url     : https://prove2.me/submissions/86ed6738-41f0-4ccf-87a5-6102a4d9d45b

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Definitions.Def_OAIQ259US001
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg2260
import Theorems.Thm_OAI_UniversalTensorSquare_sg5
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 9. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4426_oai : RowSquare [9,2,1,1,1,1,1] [5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5 sg2260

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg4426_oai := @OAI.UniversalTensorSquare.sg4426_oai
