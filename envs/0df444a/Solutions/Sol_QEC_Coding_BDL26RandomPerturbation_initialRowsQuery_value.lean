-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.initialRowsQuery_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:17:54.328831+00:00
-- url     : https://prove2.me/submissions/7ef34868-9c10-49b2-8914-e8f2333f37c1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedSteps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExecutionPrimitiveQueries
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_mapQuery_value


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation)
    (T : Table (X := fun _ : Vertex P => Space)) :
    (initialRowsQuery P T).1 = (vertexInputList P).map (fun v => (v,0,T (v,0))) :=
  mapQuery_value _ _
end QEC.Coding.BDL26RandomPerturbation
