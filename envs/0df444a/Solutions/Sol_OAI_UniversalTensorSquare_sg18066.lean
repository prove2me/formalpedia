-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg18066
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T09:07:23.324499+00:00
-- url     : https://prove2.me/submissions/bc24b438-aaca-4aa0-9c05-275c9b6893cf

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg12825
import Theorems.Thm_OAI_UniversalTensorSquare_sg26

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 43. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg18066_oai : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,5,3,3] := by
  exact rowSquare_join (by decide) sg26 sg12825

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg18066_oai := @OAI.UniversalTensorSquare.sg18066_oai
