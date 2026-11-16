-- Prove2me | solution 1 for OAI.UniversalTensorSquare.eq_diagramOfCols
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T21:32:18.940202+00:00
-- url     : https://prove2.me/submissions/6c93eee6-0f21-4cac-8738-fd23fd254289

import Mathlib
import Definitions.Def_OAIQ259US002

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_FiniteDiagrams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Diagrams. -/

section

namespace UniversalTensorSquare

lemma eq_diagramOfCols_oai (μ : YoungDiagram) (rs : List ℕ) (hs : rs.SortedGE)
    (h : μ.transpose.rowLens = rs) : μ = diagramOfCols rs hs := by
  subst rs
  simp only [diagramOfCols, YoungDiagram.ofRowLens_to_rowLens_eq_self,
    YoungDiagram.transpose_transpose]

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.eq_diagramOfCols_oai := @OAI.UniversalTensorSquare.eq_diagramOfCols_oai
