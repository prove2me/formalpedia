-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg234
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T15:41:31.776358+00:00
-- url     : https://prove2.me/submissions/b7fe2415-a47f-4c64-8db4-39e8ff8a6023

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

lemma sg234_oai : RowSquare [7] [7] := by
  exact rowSquare_trivial _ (by decide)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg234_oai := @OAI.UniversalTensorSquare.sg234_oai
