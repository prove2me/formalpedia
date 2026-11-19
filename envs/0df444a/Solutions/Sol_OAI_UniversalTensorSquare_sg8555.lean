-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg8555
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:23:03.162958+00:00
-- url     : https://prove2.me/submissions/dfa8e978-38ee-46cd-bf2d-eedbc4f2e200

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1332
import Theorems.Thm_OAI_UniversalTensorSquare_sg999

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

lemma sg8555_oai : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg999 sg1332

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg8555_oai := @OAI.UniversalTensorSquare.sg8555_oai
