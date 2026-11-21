-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg9528
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:53:40.340254+00:00
-- url     : https://prove2.me/submissions/c31e608b-1bb2-4680-9ac3-8e5dfaba66c3

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1033
import Theorems.Thm_OAI_UniversalTensorSquare_sg1767
import Definitions.Def_OAIQ259US001

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9528_oai : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,4,3] := by
  exact rowSquare_join (by decide) sg1033 sg1767

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg9528_oai := @OAI.UniversalTensorSquare.sg9528_oai
