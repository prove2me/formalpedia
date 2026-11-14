-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg22066
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T03:38:48.460634+00:00
-- url     : https://prove2.me/submissions/cf6e3a27-db4e-41b4-8285-cc40c9906846
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg6315
import Theorems.Thm_OAI_UniversalTensorSquare_sg7315

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 53. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg22066_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6315 sg7315

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg22066_oai := @OAI.UniversalTensorSquare.sg22066_oai
