-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg32977
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T04:13:08.023225+00:00
-- url     : https://prove2.me/submissions/a74b4991-ecc1-4d92-800b-d3fe197ef8c8

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17208
import Theorems.Thm_OAI_UniversalTensorSquare_sg20531

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 81. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg32977_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20531 sg17208

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg32977_oai := @OAI.UniversalTensorSquare.sg32977_oai
