-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P17.postprocessing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T12:55:30.728423+00:00
-- url     : https://prove2.me/submissions/1905b5b9-f304-4f36-876e-8435f32002d8

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P17
noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate Topology

open QAlgorithms.Papers.Independent.Advance50.P17

theorem solution {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]
  [Nonempty I] [Nonempty J] [Nonempty K] (delta : ProcessDistance) (hm : ProcessMetrics delta)
    (hc : ProcessChaining delta) (E F : FiniteProcess I J) (R : FiniteProcess J K) :
    delta (R.val ∘ E.val) (R.val ∘ F.val) ≤ delta E.val F.val := by
  have h1 := hc I J K E F R R
  have h2 : delta R.val R.val = 0 := ((hm J K).2.1 R R).2 rfl
  linarith

end
