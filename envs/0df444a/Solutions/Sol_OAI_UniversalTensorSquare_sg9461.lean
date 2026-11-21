-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg9461
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:52:21.861417+00:00
-- url     : https://prove2.me/submissions/f735b161-efa5-4b60-995e-43bdd3326a45

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1033
import Theorems.Thm_OAI_UniversalTensorSquare_sg1756
import Definitions.Def_OAIQ259US001

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9461_oai : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1033 sg1756

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg9461_oai := @OAI.UniversalTensorSquare.sg9461_oai
