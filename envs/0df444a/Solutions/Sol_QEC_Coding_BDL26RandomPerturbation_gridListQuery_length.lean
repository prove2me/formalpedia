-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.gridListQuery_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:03:43.177375+00:00
-- url     : https://prove2.me/submissions/ee41e321-1b06-48eb-8b92-64c218d91a6d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridPointQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridEnumerationQuery
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_gridCoordinateListQuery_length
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_gridPlaneQuery_length
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_flatMapQuery_value
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_flatMap_length_of_const


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (K : ℕ) : (gridListQuery K).1.length = (2*K+1)^3 := by
  rw [gridListQuery,flatMapQuery_value,flatMap_length_of_const _ _ ((2*K+1)^2)]
  · rw [gridCoordinateListQuery_length]; ring
  · intro a ha
    rw [gridPlaneQuery_length,gridCoordinateListQuery_length]
end QEC.Coding.BDL26RandomPerturbation
