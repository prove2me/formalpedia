-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg34458
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:52:22.665228+00:00
-- url     : https://prove2.me/submissions/b0c72003-424e-466d-95fc-e8c80979e4c1

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg16254
import Theorems.Thm_OAI_UniversalTensorSquare_sg20742

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 84. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg34458_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,9,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20742 sg16254

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg34458_oai := @OAI.UniversalTensorSquare.sg34458_oai
