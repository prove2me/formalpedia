-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg38281
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T15:52:12.626913+00:00
-- url     : https://prove2.me/submissions/a43df264-b4a0-474e-b2a1-a6854471440c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg19623
import Theorems.Thm_OAI_UniversalTensorSquare_sg2710
import Theorems.Thm_OAI_UniversalTensorSquare_sg4904

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 46. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg19005 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg2710 sg4904

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes94
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 94. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg38281_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,8,8,6,6,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19005

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg38281_oai := @OAI.UniversalTensorSquare.sg38281_oai
