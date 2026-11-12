-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P33.printedTableNormalization
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T19:09:48.742201+00:00
-- url     : https://prove2.me/submissions/8dfffd34-6044-4117-9075-3ec6ff50c996

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P33

open scoped BigOperators ENNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Intakethird100.P33 in
theorem solution (x pd f : ℝ) :
    (∑ pattern : Fin 4, ∑ port : Fin 2, printedCount x pd f pattern port) =
      (x / 2 + (2 - x / 2) * pd) * (1 - f) := by
  simp [Fin.sum_univ_four, Fin.sum_univ_two, printedCount, printedSignal] <;> ring
