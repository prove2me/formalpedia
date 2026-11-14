-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg217
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T02:24:10.514455+00:00
-- url     : https://prove2.me/submissions/3f586690-1238-498e-86bf-94454c812720

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

lemma sg217_oai : RowSquare [4,3] [7] := by
  exact rowSquare_trivial _ (by decide)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg217_oai := @OAI.UniversalTensorSquare.sg217_oai
