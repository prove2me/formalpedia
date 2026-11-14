-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:05:59.757676+00:00
-- url     : https://prove2.me/submissions/6a3f7a46-57c8-43a1-844b-031d31acef77

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

lemma sg1_oai : RowSquare [1,1] [2] := by
  exact rowSquare_trivial _ (by decide)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg1_oai := @OAI.UniversalTensorSquare.sg1_oai
