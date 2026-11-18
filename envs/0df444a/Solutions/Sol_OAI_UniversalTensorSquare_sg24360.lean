-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24360
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:24:44.18795+00:00
-- url     : https://prove2.me/submissions/817d44e3-099c-4512-b0e3-7a4b7eef4132
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg1330
import Theorems.Thm_OAI_UniversalTensorSquare_sg8350

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

lemma sg8554 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1001 sg1330

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 25. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10633 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8554

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

lemma sg24360_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8350 sg10633

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24360_oai := @OAI.UniversalTensorSquare.sg24360_oai
