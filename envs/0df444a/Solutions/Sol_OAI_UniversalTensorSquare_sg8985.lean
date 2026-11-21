-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg8985
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:33:34.97269+00:00
-- url     : https://prove2.me/submissions/bdb18446-5eba-4afc-959c-adc2e9c9732c

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1891
import Theorems.Thm_OAI_UniversalTensorSquare_sg911

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

lemma sg8985_oai : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg911 sg1891

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg8985_oai := @OAI.UniversalTensorSquare.sg8985_oai
