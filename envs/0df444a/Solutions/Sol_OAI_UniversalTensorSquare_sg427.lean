-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg427
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T21:42:15.451489+00:00
-- url     : https://prove2.me/submissions/2351f87a-426e-45ea-8a20-8ea3a8503a3e

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

lemma sg427_oai : RowSquare [1,1,1,1,1,1,1,1,1] [9] := by
  exact rowSquare_trivial _ (by decide)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg427_oai := @OAI.UniversalTensorSquare.sg427_oai
