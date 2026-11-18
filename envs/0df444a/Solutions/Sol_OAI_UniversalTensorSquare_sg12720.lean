-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg12720
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:17:39.011845+00:00
-- url     : https://prove2.me/submissions/968d684a-f390-4c79-85e4-b7b982d6d7cc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg6197
import Theorems.Thm_OAI_UniversalTensorSquare_sg74

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

lemma sg12720_oai : RowSquare [11,3,2,2,2,2,2,1] [5,5,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg6197

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg12720_oai := @OAI.UniversalTensorSquare.sg12720_oai
