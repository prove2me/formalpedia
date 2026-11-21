-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg26086
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T09:43:16.389387+00:00
-- url     : https://prove2.me/submissions/d9e76c3c-6908-4290-9237-5d04c6d6d14b

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10276
import Theorems.Thm_OAI_UniversalTensorSquare_sg8430

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 63. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg26086_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10276

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg26086_oai := @OAI.UniversalTensorSquare.sg26086_oai
