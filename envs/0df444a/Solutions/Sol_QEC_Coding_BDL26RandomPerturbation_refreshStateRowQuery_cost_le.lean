-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.refreshStateRowQuery_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-10T23:27:44.197055+00:00
-- url     : https://prove2.me/submissions/78ea65ab-aeeb-42fd-a7b5-c5ae45e9e519

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExecutionPrimitiveQueries
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateRows
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
variable {P : TannerSquarePresentation}
theorem solution (support : List (Vertex P))
    (T : Table (X := fun _ : Vertex P => Space)) (row : Vertex P × ℕ × Space)
    (hlen : support.length ≤ 12) : (refreshStateRowQuery support T row).2 ≤ 30 := by
  classical
  have hm : ∀ L : List (Vertex P),
      (memberQuery (fun v w : Vertex P => (decide (v=w),1)) row.1 L).2 ≤ 2*L.length := by
    intro L
    induction L with
    | nil => simp [memberQuery]
    | cons a L ih =>
      simp only [memberQuery, List.length_cons]
      split <;> simp_all <;> omega
  have h := hm support
  dsimp [refreshStateRowQuery]
  omega
