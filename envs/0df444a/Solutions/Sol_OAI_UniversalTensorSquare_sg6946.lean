-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg6946
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:17:13.46376+00:00
-- url     : https://prove2.me/submissions/374c7e8e-bfd6-4cf6-9c83-a1affc62c391

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1008
import Theorems.Thm_OAI_UniversalTensorSquare_sg998

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6946_oai : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1008

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg6946_oai := @OAI.UniversalTensorSquare.sg6946_oai
