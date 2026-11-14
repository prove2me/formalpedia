-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg122
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T21:14:40.590206+00:00
-- url     : https://prove2.me/submissions/26e85be6-e5b3-4c36-8d9e-a081fbd9b993

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

lemma sg122_oai : RowSquare [2,2,1,1,1] [7] := by
  exact rowSquare_trivial _ (by decide)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg122_oai := @OAI.UniversalTensorSquare.sg122_oai
