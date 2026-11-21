-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg33642
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T07:08:19.683491+00:00
-- url     : https://prove2.me/submissions/9c36869e-4d81-43b3-8ffd-7a91e90f3531

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg16234
import Theorems.Thm_OAI_UniversalTensorSquare_sg20728

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 82. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg33642_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,8,8,8,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20728 sg16234

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg33642_oai := @OAI.UniversalTensorSquare.sg33642_oai
