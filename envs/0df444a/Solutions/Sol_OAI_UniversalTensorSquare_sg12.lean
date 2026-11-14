-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg12
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T20:57:03.421651+00:00
-- url     : https://prove2.me/submissions/71e6d9cc-19cf-4102-8627-6afbd0077d50

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

lemma sg12_oai : RowSquare [2,1,1] [4] := by
  exact rowSquare_trivial _ (by decide)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg12_oai := @OAI.UniversalTensorSquare.sg12_oai
