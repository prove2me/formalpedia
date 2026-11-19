-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23480
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T18:13:35.912493+00:00
-- url     : https://prove2.me/submissions/6a118ff0-8629-47f6-bd03-9a385a955d75

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg52
import Theorems.Thm_OAI_UniversalTensorSquare_sg6677

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6481 : RowSquare [7,5,1,1,1,1,1,1,1] [5,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg52 sg2251

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 57. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23480_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6481 sg6677

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23480_oai := @OAI.UniversalTensorSquare.sg23480_oai
