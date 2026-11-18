-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg4058
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:55:20.217529+00:00
-- url     : https://prove2.me/submissions/1d18b9d0-9e6d-453d-9a55-f9abdfadd978

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg25

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 8. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4058_oai : RowSquare [6,4,1,1,1,1,1,1] [6,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg25 sg1327

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg4058_oai := @OAI.UniversalTensorSquare.sg4058_oai
