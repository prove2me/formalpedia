-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23842
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:03:14.799884+00:00
-- url     : https://prove2.me/submissions/3723359e-d38a-4124-a8f0-2578f4ed0a87
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg11737
import Theorems.Thm_OAI_UniversalTensorSquare_sg6394

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

lemma sg23842_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,5,5,5,5,5,3,1] := by
  exact rowSquare_join (by decide) sg6394 sg11737

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23842_oai := @OAI.UniversalTensorSquare.sg23842_oai
