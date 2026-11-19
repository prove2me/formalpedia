-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg8638
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:23:36.499844+00:00
-- url     : https://prove2.me/submissions/2b1042b1-8c2f-4a84-9282-11ec2034c91b

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg939

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

lemma sg8638_oai : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [6,6,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg939 sg1327

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg8638_oai := @OAI.UniversalTensorSquare.sg8638_oai
