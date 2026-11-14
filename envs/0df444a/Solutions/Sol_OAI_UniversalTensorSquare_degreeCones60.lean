-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeCones60
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:37:48.793958+00:00
-- url     : https://prove2.me/submissions/0ec4decd-0525-4ec5-a13c-c558512f69f2

import Mathlib
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US007

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 60. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCones60_oai : ∀ q ∈ degreeQs60, ∀ μ : YoungDiagram, μ.card = 60 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 8 6 0) μ := by
  intro q hq
  simp only [degreeQs60,List.not_mem_nil] at hq

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeCones60_oai := @OAI.UniversalTensorSquare.degreeCones60_oai
