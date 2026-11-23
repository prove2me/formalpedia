-- Prove2me | solution 1 for SumProduct.unitBox_eq_cubeSection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:52:06.269971+00:00
-- url     : https://prove2.me/submissions/7dc66308-cfc0-433b-a178-c5b6204a23a1

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_CubeSection

set_option autoImplicit true
open MeasureTheory
open scoped Pointwise
open SumProduct
variable {ι : Type*} [Fintype ι]
open scoped Classical
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
namespace SumProduct
theorem _root_.solution (K : Type*) [Field K] [NumberField K] (r : ℝ) :
    unitBox K r = cubeSection {w : InfinitePlace K // w ≠ w₀} r := rfl
end SumProduct
