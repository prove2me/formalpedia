-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.StateRowsRep_points
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T23:02:41.155473+00:00
-- url     : https://prove2.me/submissions/73541509-6de6-4383-8cbb-7a927a7b3de0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExecutionPrimitiveQueries
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateRows
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_stateRowQuery_value
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_vertexInputList_complete


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
variable {P : TannerSquarePresentation}
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (T : Table (X := fun _ : Vertex P => Space))
    (c : Counters (Vertex P)) (R : StateRows P) (hR : StateRowsRep P T c R) :
    statePoints R = assignment T c := by
  funext v
  have hm : ∃ row ∈ R, row.1=v := by
    have hv := vertexInputList_complete P v
    rw [← hR.1,List.mem_map] at hv
    exact hv
  have hv := stateRowQuery_value v R (c v,T (v,c v)) (by
    intro row hr hv
    subst v
    exact hR.2 row hr) hm
  exact congrArg Prod.snd hv
end QEC.Coding.BDL26RandomPerturbation
