-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25015
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T06:49:48.524206+00:00
-- url     : https://prove2.me/submissions/445da6a6-83db-4382-90fb-5afc708175fe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10242
import Theorems.Thm_OAI_UniversalTensorSquare_sg8429

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 61. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25015_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,6,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10242

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25015_oai := @OAI.UniversalTensorSquare.sg25015_oai
