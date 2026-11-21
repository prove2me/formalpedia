-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25547
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:53:18.963966+00:00
-- url     : https://prove2.me/submissions/ebff347a-93cc-488a-bb3e-ebe6b467bb0d

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg8648
import Theorems.Thm_OAI_UniversalTensorSquare_sg9800

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25547_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9800

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25547_oai := @OAI.UniversalTensorSquare.sg25547_oai
