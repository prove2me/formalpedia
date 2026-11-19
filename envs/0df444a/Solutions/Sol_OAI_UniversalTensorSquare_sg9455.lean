-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg9455
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:52:11.090813+00:00
-- url     : https://prove2.me/submissions/a32c2c35-2b86-4a6f-8f64-9c8f7cfcba1e

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1032
import Theorems.Thm_OAI_UniversalTensorSquare_sg1755

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9455_oai : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1032 sg1755

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg9455_oai := @OAI.UniversalTensorSquare.sg9455_oai
