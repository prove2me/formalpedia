-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24178
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:20:13.005218+00:00
-- url     : https://prove2.me/submissions/c470e2df-b3c6-49a2-a7d9-657df0e9c072
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10625
import Theorems.Thm_OAI_UniversalTensorSquare_sg8350

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

lemma sg24178_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10625

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24178_oai := @OAI.UniversalTensorSquare.sg24178_oai
