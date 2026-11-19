-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24437
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T05:28:51.052825+00:00
-- url     : https://prove2.me/submissions/718671d3-63d3-4183-aecc-7a596b4158f6

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1032
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg179

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

lemma sg4677 : RowSquare [4,4,2,1,1,1,1,1,1,1] [4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg179 sg1032

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

lemma sg8761 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg13 sg4677

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9442 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1032 sg1754

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 59. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24437_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8761 sg9442

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24437_oai := @OAI.UniversalTensorSquare.sg24437_oai
