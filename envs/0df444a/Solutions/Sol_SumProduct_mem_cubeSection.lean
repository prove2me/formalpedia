-- Prove2me | solution 1 for SumProduct.mem_cubeSection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:51:05.921624+00:00
-- url     : https://prove2.me/submissions/c6a049af-8243-4ac0-8b0c-8122c1a1e4e4

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_CubeSection

set_option autoImplicit true
open MeasureTheory
open scoped Pointwise
open SumProduct
variable {ι : Type*} [Fintype ι]
namespace SumProduct
theorem _root_.solution {r : ℝ} {y : ι → ℝ} :
    y ∈ cubeSection ι r ↔ (∀ i, |y i| ≤ r) ∧ |∑ i, y i| ≤ r := Iff.rfl
end SumProduct
