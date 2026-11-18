-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg426
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T21:35:07.792207+00:00
-- url     : https://prove2.me/submissions/d45d36d9-01cb-4486-aec6-9aba7a36774b

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

lemma sg426_oai : RowSquare [8] [8] := by
  exact rowSquare_trivial _ (by decide)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg426_oai := @OAI.UniversalTensorSquare.sg426_oai
