-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg454
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:27:22.780204+00:00
-- url     : https://prove2.me/submissions/209288b4-f394-46e2-9745-0e7a79661adb

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

lemma sg454_oai : RowSquare [3,1,1,1,1,1,1] [9] := by
  exact rowSquare_trivial _ (by decide)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg454_oai := @OAI.UniversalTensorSquare.sg454_oai
