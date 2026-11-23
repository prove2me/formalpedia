-- Prove2me | solution 1 for SumProduct.measurableSet_cubeSection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:53:21.76313+00:00
-- url     : https://prove2.me/submissions/8dc4e32d-041a-46e1-81d2-481527514d0e

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_CubeSection
import Theorems.Thm_SumProduct_isClosed_cubeSection

set_option autoImplicit true
open MeasureTheory
open scoped Pointwise
open SumProduct
variable {ι : Type*} [Fintype ι]
namespace SumProduct
theorem _root_.solution (r : ℝ) : MeasurableSet (cubeSection ι r) :=
  (isClosed_cubeSection r).measurableSet
end SumProduct
