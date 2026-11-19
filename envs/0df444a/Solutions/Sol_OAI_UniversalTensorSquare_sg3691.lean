-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg3691
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T13:49:41.709943+00:00
-- url     : https://prove2.me/submissions/ab1368fb-f1d9-4ebb-afba-e26be844c1ee

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg32

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 7. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3691_oai : RowSquare [9,2,2,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg1001

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg3691_oai := @OAI.UniversalTensorSquare.sg3691_oai
