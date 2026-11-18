-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg2063
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:52:14.619578+00:00
-- url     : https://prove2.me/submissions/49d0dc96-625e-4677-b7ce-913b296c6ccd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg179
import Theorems.Thm_OAI_UniversalTensorSquare_sg91

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2063_oai : RowSquare [4,3,1,1,1,1,1,1] [5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg91 sg179

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg2063_oai := @OAI.UniversalTensorSquare.sg2063_oai
