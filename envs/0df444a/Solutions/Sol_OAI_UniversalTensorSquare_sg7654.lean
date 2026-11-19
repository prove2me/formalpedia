-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg7654
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:46:09.736818+00:00
-- url     : https://prove2.me/submissions/25dbfffc-1190-412a-9c91-9450b4bb8dd2

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg903
import Theorems.Thm_OAI_UniversalTensorSquare_sg999
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

lemma sg7654_oai : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,6,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg903

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg7654_oai := @OAI.UniversalTensorSquare.sg7654_oai
