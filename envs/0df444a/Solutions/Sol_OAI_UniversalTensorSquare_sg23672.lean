-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23672
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T18:03:08.102197+00:00
-- url     : https://prove2.me/submissions/0afe6b7d-1a20-48d5-ad5e-d327cf5fbc80
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg23533

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 57. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23672_oai : RowSquare [11,10,4,3,2,2,2,2,2,2,1,1] [7,5,5,5,5,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg23533

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23672_oai := @OAI.UniversalTensorSquare.sg23672_oai
