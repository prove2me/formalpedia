-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T23:36:15.212225+00:00
-- url     : https://prove2.me/submissions/8ba54eb7-a9de-4763-a614-b5741efe4bce

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

lemma sg2_oai : RowSquare [2] [2] := by
  exact rowSquare_trivial _ (by decide)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg2_oai := @OAI.UniversalTensorSquare.sg2_oai
