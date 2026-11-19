-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg11212
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T17:26:54.38071+00:00
-- url     : https://prove2.me/submissions/56a9a2c3-1b7f-487c-b133-dfa8bf0279da

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1500
import Theorems.Thm_OAI_UniversalTensorSquare_sg1947

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11212_oai : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [7,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1500 sg1947

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg11212_oai := @OAI.UniversalTensorSquare.sg11212_oai
