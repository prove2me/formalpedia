-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24705
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:34:09.156946+00:00
-- url     : https://prove2.me/submissions/feb71d94-74bf-4fdd-bdf2-bba8ccccac95
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1329
import Theorems.Thm_OAI_UniversalTensorSquare_sg180
import Theorems.Thm_OAI_UniversalTensorSquare_sg809

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

lemma sg1424 : RowSquare [6,3,1,1] [3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg180

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

lemma sg8722 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg809 sg1327

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

lemma sg9504 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1424

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 60. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24705_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9504

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24705_oai := @OAI.UniversalTensorSquare.sg24705_oai
