-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg21
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T01:26:41.166192+00:00
-- url     : https://prove2.me/submissions/01af4df0-a194-4bfb-80cf-c2791c362ea1

import Mathlib
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_trivial

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

lemma sg21_oai : RowSquare [1,1,1,1,1] [5] := by
  exact rowSquare_trivial _ (by decide)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg21_oai := @OAI.UniversalTensorSquare.sg21_oai
