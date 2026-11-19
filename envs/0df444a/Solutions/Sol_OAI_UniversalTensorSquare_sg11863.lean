-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg11863
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:43:51.594223+00:00
-- url     : https://prove2.me/submissions/9263b9fe-6dcf-409b-9e2c-9cb92c729faa

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg2549
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

lemma sg11863_oai : RowSquare [8,6,2,2,2,2,1,1] [5,5,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg808 sg2549

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg11863_oai := @OAI.UniversalTensorSquare.sg11863_oai
