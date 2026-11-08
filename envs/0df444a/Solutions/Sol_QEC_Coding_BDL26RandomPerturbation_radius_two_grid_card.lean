-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.radius_two_grid_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:33:31.099917+00:00
-- url     : https://prove2.me/submissions/8b8416c1-d456-4fa3-b8ce-88e14e2df701

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Int.Interval
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_grid_card

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution : Fintype.card (Grid 2) = 125 := by
  rw [grid_card]
  norm_num
end QEC.Coding.BDL26RandomPerturbation
