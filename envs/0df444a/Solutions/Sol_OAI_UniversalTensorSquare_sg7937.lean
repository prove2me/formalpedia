-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg7937
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:01:24.377081+00:00
-- url     : https://prove2.me/submissions/e896071c-0f9b-43b1-9af2-fbb5728a11fd

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Definitions.Def_OAIQ259US001
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg115
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg5
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 0. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg118 : RowSquare [2,2,1,1,1] [4,3] := by
  exact rowSquare_join (by decide) sg5 sg17

lemma sg506 : RowSquare [3,3,1,1,1] [6,3] := by
  exact rowSquare_join (by decide) sg1 sg118

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 8. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4010 : RowSquare [5,5,2,2,2] [3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg115 sg506

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 12. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5613 : RowSquare [5,5,2,2,2,1,1] [5,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg4010

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

lemma sg7937_oai : RowSquare [7,5,2,2,2,1,1] [7,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg5613

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg7937_oai := @OAI.UniversalTensorSquare.sg7937_oai
