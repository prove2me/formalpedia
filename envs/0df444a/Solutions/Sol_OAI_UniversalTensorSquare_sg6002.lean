-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg6002
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T20:53:10.663401+00:00
-- url     : https://prove2.me/submissions/b381f30d-d8cd-4519-8c87-6acef5dbf7fb

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Definitions.Def_OAIQ259US001
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg4
import Theorems.Thm_OAI_UniversalTensorSquare_sg832
import Theorems.Thm_OAI_UniversalTensorSquare_sg89
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

lemma sg696 : RowSquare [6,2,1] [3,3,3] := by
  exact rowSquare_join (by decide) sg4 sg89

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 13. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6002_oai : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg696 sg832

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg6002_oai := @OAI.UniversalTensorSquare.sg6002_oai
