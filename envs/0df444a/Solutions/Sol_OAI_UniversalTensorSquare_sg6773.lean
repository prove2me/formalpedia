-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg6773
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:09:22.248984+00:00
-- url     : https://prove2.me/submissions/4641e3c1-0501-453b-a8c3-fd8ec20103ad

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg958
import Theorems.Thm_OAI_UniversalTensorSquare_sg999
import Definitions.Def_OAIQ259US001
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 15. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6773_oai : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg958 sg999

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg6773_oai := @OAI.UniversalTensorSquare.sg6773_oai
