-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T21:19:36.224836+00:00
-- url     : https://prove2.me/submissions/bee411a1-d9bd-496b-b31d-3db6515fd573

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

lemma sg3_oai : RowSquare [1,1,1] [3] := by
  exact rowSquare_trivial _ (by decide)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg3_oai := @OAI.UniversalTensorSquare.sg3_oai
