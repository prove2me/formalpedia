-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T14:52:21.377225+00:00
-- url     : https://prove2.me/submissions/885e21d2-367e-45e4-89a6-e321bd41e085

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

lemma sg238_oai : RowSquare [2,1,1,1,1,1,1] [8] := by
  exact rowSquare_trivial _ (by decide)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg238_oai := @OAI.UniversalTensorSquare.sg238_oai
