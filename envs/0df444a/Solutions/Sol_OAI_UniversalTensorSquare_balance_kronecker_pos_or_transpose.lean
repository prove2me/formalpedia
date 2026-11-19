-- Prove2me | solution 1 for OAI.UniversalTensorSquare.balance_kronecker_pos_or_transpose
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T17:16:39.527608+00:00
-- url     : https://prove2.me/submissions/763be7ee-22bf-4f9a-ae87-ed88ce10e624

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_UniversalTensorSquare_balance_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_kronecker_pos_transpose_iff

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceFour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Four. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns Saxl.FlagColumns

theorem balance_kronecker_pos_or_transpose_oai {n M b δ : ℕ} (hM : 9 ≤ M)
    (hb : b ≤ M-2) (hδ : δ ≤ 1) (hn : (candidate M b δ).card = n)
    (μ : YoungDiagram) (hμ : μ.card = n)
    (hsmall : colPrefix μ 4 ≤ 2*M-2 ∨ colPrefix μ.transpose 4 ≤ 2*M-2) :
    0 < kronecker (canonicalTableau (candidate M b δ) hn)
      (canonicalTableau (candidate M b δ) hn) (canonicalTableau μ hμ) := by
  rcases hsmall with h | h
  · exact balance_kronecker_pos hM hb hδ _ μ _ h
  · have hpos := balance_kronecker_pos hM hb hδ (canonicalTableau (candidate M b δ) hn)
      μ.transpose (canonicalTableau μ.transpose ((transpose_card μ).trans hμ)) h
    exact (kronecker_pos_transpose_iff _ hn (candidate_transpose M b δ) μ hμ).mpr hpos

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.balance_kronecker_pos_or_transpose_oai := @OAI.UniversalTensorSquare.balance_kronecker_pos_or_transpose_oai
