-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T06:49:25.022798+00:00
-- url     : https://prove2.me/submissions/0b752cb1-2251-4284-bfb3-8ad63a77410e

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

lemma sg25_oai : RowSquare [2,1,1,1] [5] := by
  exact rowSquare_trivial _ (by decide)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25_oai := @OAI.UniversalTensorSquare.sg25_oai
