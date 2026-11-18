-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg2706
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:17:57.095496+00:00
-- url     : https://prove2.me/submissions/65ee6cfb-38c3-4113-9604-70c8d89d0098
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg105
import Theorems.Thm_OAI_UniversalTensorSquare_sg236

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2706_oai : RowSquare [7,2,1,1,1,1,1] [2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg105 sg236

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg2706_oai := @OAI.UniversalTensorSquare.sg2706_oai
