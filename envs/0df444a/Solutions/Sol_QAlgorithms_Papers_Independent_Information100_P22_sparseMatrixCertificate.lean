-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P22.sparseMatrixCertificate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:00:27.172958+00:00
-- url     : https://prove2.me/submissions/84542f02-9604-4ab9-81e4-083c530d0cd6

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

open QAlgorithms.Papers.Independent.Information100.P22 in
theorem solution : sparseCutMatrix.rank = 12 := by
  let N : Matrix (Fin 12) (Fin 12) F2 :=
    ![![0,0,0,0,0,1,0,0,0,0,1,0], ![0,0,0,1,1,1,0,0,1,0,1,0], ![0,0,0,0,1,1,1,1,1,0,1,1], ![0,0,0,0,0,0,0,0,0,0,1,0], ![0,0,0,1,1,0,1,0,1,0,0,1], ![1,1,1,1,0,0,1,1,1,1,0,1], ![0,0,1,0,0,1,0,0,0,1,1,0], ![1,1,0,1,0,1,1,1,0,1,1,1], ![1,1,1,0,0,0,1,1,1,1,1,1], ![1,1,1,0,1,1,0,1,1,1,0,1], ![0,0,0,0,0,1,0,0,0,0,0,1], ![0,1,1,1,1,1,1,0,1,0,1,1]]
  have h : sparseCutMatrix * N = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hu : IsUnit sparseCutMatrix :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse h)
  rw [Matrix.rank_of_isUnit _ hu, Fintype.card_fin]
