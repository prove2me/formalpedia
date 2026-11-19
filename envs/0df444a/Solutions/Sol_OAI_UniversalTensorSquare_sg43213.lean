-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg43213
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T20:18:40.218824+00:00
-- url     : https://prove2.me/submissions/ab2c5fb4-733d-43db-96e8-26277423fd57

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1006
import Theorems.Thm_OAI_UniversalTensorSquare_sg18910
import Theorems.Thm_OAI_UniversalTensorSquare_sg371
import Theorems.Thm_OAI_UniversalTensorSquare_sg489
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Definitions.Def_OAIQ259US001

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 2. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1507 : RowSquare [7,1,1,1,1] [4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1006

lemma sg1553 : RowSquare [8,1,1,1] [5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg371

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 21. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8980 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1507 sg1553

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 49. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20309 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,7,4,3,3,3] := by
  exact rowSquare_join (by decide) sg489 sg8980

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 106. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg43213_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [14,10,7,6,6,6,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20309

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg43213_oai := @OAI.UniversalTensorSquare.sg43213_oai
