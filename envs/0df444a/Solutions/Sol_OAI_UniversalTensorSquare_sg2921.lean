-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg2921
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T02:41:11.804012+00:00
-- url     : https://prove2.me/submissions/5a2e5c47-8cb4-49fb-941c-e3c2feda7165

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg315
import Theorems.Thm_OAI_UniversalTensorSquare_sg88

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 6. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2921_oai : RowSquare [8,2,2,1,1] [4,4,3,3] := by
  exact rowSquare_join (by decide) sg88 sg315

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg2921_oai := @OAI.UniversalTensorSquare.sg2921_oai
