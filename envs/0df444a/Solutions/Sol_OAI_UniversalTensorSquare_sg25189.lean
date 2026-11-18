-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25189
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:45:10.061202+00:00
-- url     : https://prove2.me/submissions/867ed41a-3e51-4bbd-8fad-9bbc5af05d1f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1041
import Theorems.Thm_OAI_UniversalTensorSquare_sg1756
import Theorems.Thm_OAI_UniversalTensorSquare_sg8721

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

lemma sg9519 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1041 sg1756

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 61. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25189_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9519

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25189_oai := @OAI.UniversalTensorSquare.sg25189_oai
