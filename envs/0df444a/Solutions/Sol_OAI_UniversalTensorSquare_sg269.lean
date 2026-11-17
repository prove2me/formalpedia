-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg269
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T11:27:10.25421+00:00
-- url     : https://prove2.me/submissions/c708b254-7fe6-41b4-a1aa-a8d882b74a10

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

lemma sg269_oai : RowSquare [3,1,1,1,1,1] [8] := by
  exact rowSquare_trivial _ (by decide)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg269_oai := @OAI.UniversalTensorSquare.sg269_oai
