-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg12187
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:26:47.187691+00:00
-- url     : https://prove2.me/submissions/d8c26b17-9e0c-446b-8486-e30bca70b6f8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg2586
import Theorems.Thm_OAI_UniversalTensorSquare_sg768

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 29. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12187_oai : RowSquare [8,6,2,2,2,2,1,1] [7,7,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg768 sg2586

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg12187_oai := @OAI.UniversalTensorSquare.sg12187_oai
