-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg8730
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:28:14.614585+00:00
-- url     : https://prove2.me/submissions/4a75c5f0-0d1b-4909-a2f5-7682f2b6c550

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Definitions.Def_OAIQ259US001
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg179
import Theorems.Thm_OAI_UniversalTensorSquare_sg4

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 1. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg812 : RowSquare [4,2,1,1,1,1] [3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg179

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sg8730_oai : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg812 sg1327

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg8730_oai := @OAI.UniversalTensorSquare.sg8730_oai
