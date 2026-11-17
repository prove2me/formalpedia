-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg2573
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T08:18:57.942926+00:00
-- url     : https://prove2.me/submissions/18295c69-4efc-4e6d-9e51-af2187443d72

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

lemma sg2573_oai : RowSquare [4,4,1,1,1,1,1,1] [14] := by
  exact rowSquare_trivial _ (by decide)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg2573_oai := @OAI.UniversalTensorSquare.sg2573_oai
