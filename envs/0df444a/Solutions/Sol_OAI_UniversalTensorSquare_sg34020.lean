-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg34020
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T07:58:25.420763+00:00
-- url     : https://prove2.me/submissions/f9ab45e1-ab53-4dfc-b5e0-a1dccf5abce3

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg16237
import Theorems.Thm_OAI_UniversalTensorSquare_sg20742

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 83. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg34020_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,9,9,9,7,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20742 sg16237

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg34020_oai := @OAI.UniversalTensorSquare.sg34020_oai
