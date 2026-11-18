-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg37691
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T14:53:02.081219+00:00
-- url     : https://prove2.me/submissions/5072a4b4-abaf-403f-b37e-7634da091fd8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg13776
import Theorems.Thm_OAI_UniversalTensorSquare_sg20524

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 42. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg17403 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,4] := by
  exact rowSquare_join (by decide) sg13 sg13776

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes92
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 92. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg37691_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,9,9,8,7,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20524 sg17403

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg37691_oai := @OAI.UniversalTensorSquare.sg37691_oai
