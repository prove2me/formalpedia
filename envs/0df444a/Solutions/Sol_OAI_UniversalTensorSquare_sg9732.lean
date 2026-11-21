-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg9732
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:03:24.429496+00:00
-- url     : https://prove2.me/submissions/29ab2307-a839-4bf9-96ad-bef08c97d1ba

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1388

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

lemma sg9732_oai : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1388

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg9732_oai := @OAI.UniversalTensorSquare.sg9732_oai
