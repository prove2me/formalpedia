-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.initialRowsQuery_rep
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-10T23:48:45.10373+00:00
-- url     : https://prove2.me/submissions/19e33911-4d19-4ee4-a631-dabac7f64aeb

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExecutionPrimitiveQueries
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateRows
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
variable {P : TannerSquarePresentation}
theorem solution (P : TannerSquarePresentation) (T : Table (X := fun _ : Vertex P => Space)) :
    StateRowsRep P T (fun _ => 0) (initialRowsQuery P T).1 := by
  have hm : ∀ L : List (Vertex P),
      (mapQuery (fun v : Vertex P => ((v,0,T (v,0)),4)) L).1 =
        L.map (fun v => (v,0,T (v,0))) := by
    intro L
    induction L with
    | nil => rfl
    | cons a L ih => simp [mapQuery, ih]
  unfold StateRowsRep initialRowsQuery
  rw [hm]
  constructor
  · simp [List.map_map, Function.comp_def]
  · intro row hr
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
    rfl
