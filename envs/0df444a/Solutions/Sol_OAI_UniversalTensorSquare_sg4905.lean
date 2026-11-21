-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg4905
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T20:33:42.343219+00:00
-- url     : https://prove2.me/submissions/be5fbfc6-7564-464a-bd8a-f309ef12d64e

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Definitions.Def_OAIQ259US001
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg5
import Theorems.Thm_OAI_UniversalTensorSquare_sg892
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 4. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2164 : RowSquare [6,2,1,1,1,1,1] [4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg892

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 10. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4905_oai : RowSquare [8,4,1,1,1,1,1] [5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg2164

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg4905_oai := @OAI.UniversalTensorSquare.sg4905_oai
