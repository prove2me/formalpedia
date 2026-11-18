-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg10492
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:33:55.379629+00:00
-- url     : https://prove2.me/submissions/a6097deb-ac28-48e6-aca6-26dd033d250d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg891
import Theorems.Thm_OAI_UniversalTensorSquare_sg892

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

lemma sg1336 : RowSquare [6,1,1,1,1,1] [3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg891

lemma sg1358 : RowSquare [6,1,1,1,1,1] [5,5,1] := by
  exact rowSquare_join (by decide) sg0 sg892

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

lemma sg10492_oai : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,7,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1336 sg1358

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg10492_oai := @OAI.UniversalTensorSquare.sg10492_oai
