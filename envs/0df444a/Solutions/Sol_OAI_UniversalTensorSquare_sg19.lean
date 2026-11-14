-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg19
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T23:30:38.29346+00:00
-- url     : https://prove2.me/submissions/2c1eea69-49cc-4a84-9244-f9b0eb3566d4

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

lemma sg19_oai : RowSquare [3,1] [4] := by
  exact rowSquare_trivial _ (by decide)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg19_oai := @OAI.UniversalTensorSquare.sg19_oai
