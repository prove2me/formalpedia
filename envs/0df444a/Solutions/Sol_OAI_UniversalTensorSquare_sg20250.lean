-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg20250
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T12:32:24.532932+00:00
-- url     : https://prove2.me/submissions/4f480245-8653-45f7-8593-7870cacbedcb

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg11219
import Theorems.Thm_OAI_UniversalTensorSquare_sg275

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 49. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20250_oai : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg275 sg11219

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg20250_oai := @OAI.UniversalTensorSquare.sg20250_oai
