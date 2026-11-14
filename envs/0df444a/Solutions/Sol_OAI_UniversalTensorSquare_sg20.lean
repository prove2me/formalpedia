-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg20
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T23:36:17.896383+00:00
-- url     : https://prove2.me/submissions/e737e49e-7aac-41f7-b5fe-ed301ec02758

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

lemma sg20_oai : RowSquare [4] [4] := by
  exact rowSquare_trivial _ (by decide)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg20_oai := @OAI.UniversalTensorSquare.sg20_oai
