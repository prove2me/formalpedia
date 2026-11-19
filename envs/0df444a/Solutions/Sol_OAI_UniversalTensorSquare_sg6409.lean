-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg6409
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:01:14.563355+00:00
-- url     : https://prove2.me/submissions/4d7df4dd-d139-4d75-ad5f-3d7214d67c5c

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg808

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6409_oai : RowSquare [6,5,2,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg808

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg6409_oai := @OAI.UniversalTensorSquare.sg6409_oai
