-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg26
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T09:07:29.47821+00:00
-- url     : https://prove2.me/submissions/7a2964e5-451b-4b33-b05a-bbb90c2095f0

import Mathlib
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLocalLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Local Leaves. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg26_oai : RowSquare [2,2,1] [2,1,1,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg26_oai := @OAI.UniversalTensorSquare.sg26_oai
