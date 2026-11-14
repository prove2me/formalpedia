-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg10403
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T22:19:30.959393+00:00
-- url     : https://prove2.me/submissions/d867b6b0-584b-48d2-9f18-c2681b47ffef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1329
import Theorems.Thm_OAI_UniversalTensorSquare_sg1358

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

lemma sg10403_oai : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,7,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1358

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg10403_oai := @OAI.UniversalTensorSquare.sg10403_oai
