-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg43216
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:20:05.65219+00:00
-- url     : https://prove2.me/submissions/fe914438-2631-42df-a722-7df10fb848a0

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg18910
import Theorems.Thm_OAI_UniversalTensorSquare_sg20310

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 106. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg43216_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [14,10,7,7,5,5,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20310

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg43216_oai := @OAI.UniversalTensorSquare.sg43216_oai
