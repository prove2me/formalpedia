-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg8564
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:23:14.362921+00:00
-- url     : https://prove2.me/submissions/d9cb2466-de45-4af1-937e-22af3913ca6a

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg6906

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

lemma sg8564_oai : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg6906

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg8564_oai := @OAI.UniversalTensorSquare.sg8564_oai
