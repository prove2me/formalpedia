-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24209
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:20:42.685197+00:00
-- url     : https://prove2.me/submissions/d518a012-ba89-4944-a49f-98c7eaca2420
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg11439
import Theorems.Thm_OAI_UniversalTensorSquare_sg841
import Theorems.Thm_OAI_UniversalTensorSquare_sg998

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

lemma sg7244 : RowSquare [5,5,2,2,1,1,1,1,1,1] [4,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg841

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

lemma sg24209_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,4,3,3] := by
  exact rowSquare_join (by decide) sg7244 sg11439

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24209_oai := @OAI.UniversalTensorSquare.sg24209_oai
