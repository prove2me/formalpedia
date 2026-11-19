-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg6787
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:10:07.580273+00:00
-- url     : https://prove2.me/submissions/8dde2a18-13ef-45b3-85c7-6882cd6493ec

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1032
import Theorems.Thm_OAI_UniversalTensorSquare_sg915
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

lemma sg6787_oai : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1032 sg915

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg6787_oai := @OAI.UniversalTensorSquare.sg6787_oai
