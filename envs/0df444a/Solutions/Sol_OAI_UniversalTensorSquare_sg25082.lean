-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25082
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T06:56:42.073934+00:00
-- url     : https://prove2.me/submissions/744a69c6-7998-44a8-aa66-014eb4676b34

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg15521
import Theorems.Thm_OAI_UniversalTensorSquare_sg2224

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

lemma sg25082_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2224 sg15521

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25082_oai := @OAI.UniversalTensorSquare.sg25082_oai
