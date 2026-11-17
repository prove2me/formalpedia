-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg3239
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T02:59:13.240947+00:00
-- url     : https://prove2.me/submissions/68846e54-e406-40f9-84ac-26fe320844a5

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

lemma sg3239_oai : RowSquare [4,4,2,1,1,1,1,1] [15] := by
  exact rowSquare_trivial _ (by decide)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg3239_oai := @OAI.UniversalTensorSquare.sg3239_oai
