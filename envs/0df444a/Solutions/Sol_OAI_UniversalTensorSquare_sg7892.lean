-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg7892
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:54:30.645285+00:00
-- url     : https://prove2.me/submissions/40cfb410-e754-468e-96ff-8e19d3880c65

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Definitions.Def_OAIQ259US001
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg120
import Theorems.Thm_OAI_UniversalTensorSquare_sg151
import Theorems.Thm_OAI_UniversalTensorSquare_sg5

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2601 : RowSquare [5,4,2,2,1] [2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg151 sg120

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

lemma sg4799 : RowSquare [5,4,2,2,2,1,1] [4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg2601

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7892_oai : RowSquare [7,5,2,2,2,1,1] [6,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg4799

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg7892_oai := @OAI.UniversalTensorSquare.sg7892_oai
