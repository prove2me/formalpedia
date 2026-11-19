-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg11849
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:43:43.307387+00:00
-- url     : https://prove2.me/submissions/35ad396c-d704-42bc-917c-f5a3c22de48c

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg2547
import Theorems.Thm_OAI_UniversalTensorSquare_sg808

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 28. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11849_oai : RowSquare [8,6,2,2,2,2,1,1] [5,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg808 sg2547

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg11849_oai := @OAI.UniversalTensorSquare.sg11849_oai
