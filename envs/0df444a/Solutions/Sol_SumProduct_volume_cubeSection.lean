-- Prove2me | solution 1 for SumProduct.volume_cubeSection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:53:46.324531+00:00
-- url     : https://prove2.me/submissions/2ae3fef7-4f60-46c1-aa7e-ef7f242f3393

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_CubeSection
import Theorems.Thm_SumProduct_cubeSection_smul

set_option autoImplicit true
open MeasureTheory
open scoped Pointwise
open SumProduct
variable {ι : Type*} [Fintype ι]
namespace SumProduct
theorem _root_.solution (r : ℝ) (hr : 0 ≤ r) :
    volume (cubeSection ι r)
      = ENNReal.ofReal (r ^ Fintype.card ι) * volume (cubeSection ι 1) := by
  have hfin : Module.finrank ℝ (ι → ℝ) = Fintype.card ι := Module.finrank_pi ℝ
  rw [cubeSection_smul r hr,
    Measure.addHaar_smul_of_nonneg (μ := volume) (s := cubeSection ι 1) hr, hfin]
end SumProduct
