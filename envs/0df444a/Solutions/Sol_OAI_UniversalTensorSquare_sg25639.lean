-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25639
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T08:08:24.625494+00:00
-- url     : https://prove2.me/submissions/1cbdf70b-a960-49b2-b533-3d3fb556cfec

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10230
import Theorems.Thm_OAI_UniversalTensorSquare_sg8434

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25639_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8434 sg10230

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25639_oai := @OAI.UniversalTensorSquare.sg25639_oai
