-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg2050
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:50:13.084439+00:00
-- url     : https://prove2.me/submissions/c56a10ca-c18e-4ea5-a113-def607c0d645

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg179
import Theorems.Thm_OAI_UniversalTensorSquare_sg89

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2050_oai : RowSquare [4,3,1,1,1,1,1,1] [4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg179

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg2050_oai := @OAI.UniversalTensorSquare.sg2050_oai
