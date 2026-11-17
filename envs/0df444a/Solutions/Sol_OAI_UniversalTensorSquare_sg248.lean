-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg248
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T06:14:47.719521+00:00
-- url     : https://prove2.me/submissions/a75cf214-f3d8-4929-a856-d3e01f54285c

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

lemma sg248_oai : RowSquare [2,2,1,1,1,1] [8] := by
  exact rowSquare_trivial _ (by decide)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg248_oai := @OAI.UniversalTensorSquare.sg248_oai
