-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg11203
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T01:19:15.631817+00:00
-- url     : https://prove2.me/submissions/a297b2cd-bdf0-4cda-9b18-372008d9395f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1498
import Theorems.Thm_OAI_UniversalTensorSquare_sg1945

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11203_oai : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1498 sg1945

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg11203_oai := @OAI.UniversalTensorSquare.sg11203_oai
