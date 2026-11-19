-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg4846
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T20:30:44.905717+00:00
-- url     : https://prove2.me/submissions/b2a69a8a-eace-4616-babe-22d833459d34

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg889

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

lemma sg4846_oai : RowSquare [6,4,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg889

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg4846_oai := @OAI.UniversalTensorSquare.sg4846_oai
