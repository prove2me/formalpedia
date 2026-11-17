-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg2548
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T07:57:17.136748+00:00
-- url     : https://prove2.me/submissions/7d167fe5-0665-4584-9f84-8cd93d082ad7

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg180

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2548_oai : RowSquare [4,4,1,1,1,1,1,1] [3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg180

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg2548_oai := @OAI.UniversalTensorSquare.sg2548_oai
