-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.gridPlaneQuery_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:59:30.86949+00:00
-- url     : https://prove2.me/submissions/ae7ae476-b9ef-4d04-9a5b-ef6383f5f351

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridPointQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridEnumerationQuery
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_gridRowQuery_length
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_flatMapQuery_value
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_flatMap_length_of_const


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {K : ℕ} (L : List (GridCoordinate K)) (a : GridCoordinate K) :
    (gridPlaneQuery L a).1.length = L.length^2 := by
  rw [gridPlaneQuery,flatMapQuery_value,flatMap_length_of_const L _ L.length
    (fun b hb => gridRowQuery_length L a b)]
  ring
end QEC.Coding.BDL26RandomPerturbation
