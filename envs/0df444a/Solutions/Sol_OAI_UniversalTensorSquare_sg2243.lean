-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg2243
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:03:26.352435+00:00
-- url     : https://prove2.me/submissions/b2bd1b4c-9aea-46aa-9e72-75a3aaf88081
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg5
import Theorems.Thm_OAI_UniversalTensorSquare_sg880

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 4. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2243_oai : RowSquare [6,5,1,1] [5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg880

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg2243_oai := @OAI.UniversalTensorSquare.sg2243_oai
