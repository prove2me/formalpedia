-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg12006
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:45:57.064591+00:00
-- url     : https://prove2.me/submissions/85247473-a559-4cf1-b6cd-af6d63146834
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg2552
import Theorems.Thm_OAI_UniversalTensorSquare_sg808

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 28. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12006_oai : RowSquare [8,6,2,2,2,2,1,1] [6,5,5,4,2,2] := by
  exact rowSquare_join (by decide) sg808 sg2552

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg12006_oai := @OAI.UniversalTensorSquare.sg12006_oai
