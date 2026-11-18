-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg29438
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T02:44:44.168426+00:00
-- url     : https://prove2.me/submissions/2e5fccfe-6168-4bc8-a133-8f36f1e54711
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg1006
import Theorems.Thm_OAI_UniversalTensorSquare_sg589
import Theorems.Thm_OAI_UniversalTensorSquare_sg8415

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

lemma sg1004 : RowSquare [6,1,1,1,1] [3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg589

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6986 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1004 sg1006

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10458 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6986

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 72. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg29438_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10458

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg29438_oai := @OAI.UniversalTensorSquare.sg29438_oai
