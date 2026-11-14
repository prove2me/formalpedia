-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg15
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T22:23:51.991091+00:00
-- url     : https://prove2.me/submissions/92d1bb18-36ee-4c6d-9ec4-ccd76a83307e

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

lemma sg15_oai : RowSquare [2,2] [4] := by
  exact rowSquare_trivial _ (by decide)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg15_oai := @OAI.UniversalTensorSquare.sg15_oai
