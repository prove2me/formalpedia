-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.vertexInputList_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T22:50:57.079266+00:00
-- url     : https://prove2.me/submissions/35fb8c1e-9e60-4c10-be6a-588401af3343

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedSteps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExecutionPrimitiveQueries

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (v : Vertex P) :
    v ∈ vertexInputList P :=
  List.mem_ofFn.mpr ⟨Fintype.equivFin _ v,(Fintype.equivFin _).symm_apply_apply v⟩
end QEC.Coding.BDL26RandomPerturbation
