-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.refreshStateRowQuery_member
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-10T23:26:58.858051+00:00
-- url     : https://prove2.me/submissions/24661d62-0ab6-48c1-875b-7b40789168b7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExecutionPrimitiveQueries
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateRows
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
variable {P : TannerSquarePresentation}
theorem solution (support : List (Vertex P)) (v : Vertex P) :
    (memberQuery (fun v w : Vertex P => (decide (v=w),1)) v support).1 = true ↔ v ∈ support := by
  classical
  induction support with
  | nil => simp [memberQuery]
  | cons a L ih =>
    by_cases h : v = a
    · simp [memberQuery, h]
    · simp [memberQuery, h, ih]
