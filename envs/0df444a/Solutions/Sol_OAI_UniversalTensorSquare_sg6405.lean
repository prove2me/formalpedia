-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg6405
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:01:08.778184+00:00
-- url     : https://prove2.me/submissions/b54332c6-8cb6-46c1-81c2-48f4b6a32632

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg589
import Theorems.Thm_OAI_UniversalTensorSquare_sg891
import Definitions.Def_OAIQ259US001

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6405_oai : RowSquare [6,5,1,1,1,1,1,1,1,1] [4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg589 sg891

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg6405_oai := @OAI.UniversalTensorSquare.sg6405_oai
