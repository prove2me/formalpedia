-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg20248
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T13:52:57.159102+00:00
-- url     : https://prove2.me/submissions/48dd71c1-5485-463b-af3e-0c33b224a29b

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg11203
import Theorems.Thm_OAI_UniversalTensorSquare_sg280

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 49. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20248_oai : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg280 sg11203

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg20248_oai := @OAI.UniversalTensorSquare.sg20248_oai
