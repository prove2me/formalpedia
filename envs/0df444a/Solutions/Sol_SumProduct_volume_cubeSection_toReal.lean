-- Prove2me | solution 1 for SumProduct.volume_cubeSection_toReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:55:15.438239+00:00
-- url     : https://prove2.me/submissions/3c974abb-4b9d-4478-a815-d107dbbc8bd5

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_CubeSection
import Theorems.Thm_SumProduct_volume_cubeSection

set_option autoImplicit true
open MeasureTheory
open scoped Pointwise
open SumProduct
variable {ι : Type*} [Fintype ι]
namespace SumProduct
theorem _root_.solution (r : ℝ) (hr : 0 ≤ r) :
    (volume (cubeSection ι r)).toReal
      = r ^ Fintype.card ι * (volume (cubeSection ι 1)).toReal := by
  rw [volume_cubeSection r hr, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr _)]
end SumProduct
