-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg9195
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:42:07.414+00:00
-- url     : https://prove2.me/submissions/869db0df-b144-4b22-baed-e70bde233c49
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg2297
import Theorems.Thm_OAI_UniversalTensorSquare_sg587
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 21. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9195_oai : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg2297

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg9195_oai := @OAI.UniversalTensorSquare.sg9195_oai
