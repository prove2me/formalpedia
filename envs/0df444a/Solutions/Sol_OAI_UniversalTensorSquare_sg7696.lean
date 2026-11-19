-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg7696
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:49:13.7395+00:00
-- url     : https://prove2.me/submissions/3d4662a9-646f-42f4-90c7-54417b9b748e

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg5397

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 17. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7696_oai : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5397

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg7696_oai := @OAI.UniversalTensorSquare.sg7696_oai
