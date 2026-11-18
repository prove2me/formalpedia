-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg3709
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T14:19:09.82603+00:00
-- url     : https://prove2.me/submissions/fc5bfd72-a39d-47d7-8267-ee3f7fb030ae

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg180
import Theorems.Thm_OAI_UniversalTensorSquare_sg372

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

lemma sg3709_oai : RowSquare [9,2,2,2] [4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg180 sg372

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg3709_oai := @OAI.UniversalTensorSquare.sg3709_oai
