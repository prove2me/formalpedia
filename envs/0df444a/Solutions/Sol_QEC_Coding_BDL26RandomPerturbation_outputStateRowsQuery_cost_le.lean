-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.outputStateRowsQuery_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-10T23:27:42.630503+00:00
-- url     : https://prove2.me/submissions/cedce9aa-a3e6-4325-b0c0-ecbd51d1b60e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExecutionPrimitiveQueries
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateRows
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
variable {P : TannerSquarePresentation}
theorem solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (R : StateRows P) : (outputStateRowsQuery P J lambda R).2 ≤ 49*R.length := by
  induction R with
  | nil => simp [outputStateRowsQuery, mapQuery]
  | cons a R ih =>
    simp [outputStateRowsQuery, mapQuery, pointSnapshotQuery, snapshotCoordinateExpr, RealExpr.run] at *
    omega
