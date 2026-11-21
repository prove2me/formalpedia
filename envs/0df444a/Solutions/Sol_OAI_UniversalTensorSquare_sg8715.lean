-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg8715
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:27:46.146623+00:00
-- url     : https://prove2.me/submissions/66326136-b676-48df-ab36-fbcb777a20f5

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Definitions.Def_OAIQ259US001
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1328
import Theorems.Thm_OAI_UniversalTensorSquare_sg903
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 20. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8715_oai : RowSquare [6,6,1,1,1,1,1,1,1,1,1] [6,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg903 sg1328

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg8715_oai := @OAI.UniversalTensorSquare.sg8715_oai
