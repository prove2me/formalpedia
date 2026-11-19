-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg4979
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T20:34:39.428881+00:00
-- url     : https://prove2.me/submissions/3c4b2db3-032b-49b9-95a6-9c68a5f344ce

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg371
import Theorems.Thm_OAI_UniversalTensorSquare_sg551

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 11. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4979_oai : RowSquare [9,3,3,2] [4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg371 sg551

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg4979_oai := @OAI.UniversalTensorSquare.sg4979_oai
