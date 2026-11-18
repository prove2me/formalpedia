-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg4734
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:27:47.548312+00:00
-- url     : https://prove2.me/submissions/3e3bb4c9-c47b-4581-a3d7-c4e8eb9e4e22

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1682
import Theorems.Thm_OAI_UniversalTensorSquare_sg32

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 10. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4734_oai : RowSquare [5,3,3,2,1,1,1,1] [2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1682

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg4734_oai := @OAI.UniversalTensorSquare.sg4734_oai
