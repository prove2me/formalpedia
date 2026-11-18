-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg12925
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:17:46.4504+00:00
-- url     : https://prove2.me/submissions/f19437ba-b678-40c8-b6b5-32719a9b4bf9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg2706

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 30. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12925_oai : RowSquare [7,6,2,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg2706

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg12925_oai := @OAI.UniversalTensorSquare.sg12925_oai
