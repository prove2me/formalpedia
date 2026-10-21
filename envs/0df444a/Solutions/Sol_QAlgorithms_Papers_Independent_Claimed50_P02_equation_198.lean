-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P02.equation_198
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:22:58.61566+00:00
-- url     : https://prove2.me/submissions/45dae265-09fd-48a4-82a1-21398c548466

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P02
open QAlgorithms.Papers.Independent.Claimed50.P02

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P69 (Sites choi)

noncomputable section

theorem solution {d p q : ℕ} (hd : 2 ≤ d) (pi : Diagram p q)
    (i j : (Sites (Fin d) (p+q))) :
    Matrix.trace (diagramMatrix d pi * Matrix.single i j 1) =
      relationMatrix d (traceConnectivity ∅ pi) j i := by
  rw [Matrix.trace_mul_comm, Matrix.trace_single_mul]
  simp [diagramMatrix]

end
