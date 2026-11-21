-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23825
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:14:50.656198+00:00
-- url     : https://prove2.me/submissions/c5f0834a-ba34-44a7-b218-feda2674398a

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg8861
import Theorems.Thm_OAI_UniversalTensorSquare_sg8985

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 58. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23825_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,5,5,5,4,4,3,3] := by
  exact rowSquare_join (by decide) sg8861 sg8985

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23825_oai := @OAI.UniversalTensorSquare.sg23825_oai
