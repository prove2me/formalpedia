-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.maDet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:29.540029+00:00
-- url     : https://prove2.me/submissions/5c2d1fda-4277-4455-89f5-02129fdfc9ba

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_Lemmata_DetMonotoneStarMulSelf_OneLeReDetOneAdd
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetMonoDetOneAdd
import Theorems.Thm_Bl_DetMonotoneStarMulSelf_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open Matrix
open scoped ComplexOrder MatrixOrder
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (n : ℕ) : DetMonoStatement n := by
  first | exact Bl.DetMonotoneStarMulSelf.goal1 .. | (apply Bl.DetMonotoneStarMulSelf.goal1 <;> assumption) | (intros; apply Bl.DetMonotoneStarMulSelf.goal1 <;> assumption)
end ReciprocityTheory.L2DbarEstimates.I
