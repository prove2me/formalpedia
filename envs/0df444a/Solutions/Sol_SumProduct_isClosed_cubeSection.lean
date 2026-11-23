-- Prove2me | solution 1 for SumProduct.isClosed_cubeSection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:51:52.643381+00:00
-- url     : https://prove2.me/submissions/f4f6e112-081f-48d0-8000-36b87587db4e

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_CubeSection
import Theorems.Thm_SumProduct_mem_cubeSection
import Theorems.Thm_SumProduct_mem_boxMult
attribute [local simp] SumProduct.mem_boxMult


attribute [local simp] SumProduct.mem_cubeSection

set_option autoImplicit true
open MeasureTheory
open scoped Pointwise
open SumProduct
variable {ι : Type*} [Fintype ι]
namespace SumProduct
theorem _root_.solution (r : ℝ) : IsClosed (cubeSection ι r) := by
  rw [cubeSection, Set.setOf_and]
  refine IsClosed.inter ?_ ?_
  · rw [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
  · exact isClosed_le (by fun_prop) continuous_const
end SumProduct
