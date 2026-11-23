-- Prove2me | solution 1 for SumProduct.hensley_unitBox_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:31:29.14036+00:00
-- url     : https://prove2.me/submissions/8cd874ac-37d4-4916-8839-cf3abd18d6f7

import Definitions.Def_SumProduct_CubeSectionCore
import Definitions.Def_SumProduct_CubeSectionHensley
import Theorems.Thm_SumProduct_hensley_unitBox_volume_proof

set_option autoImplicit true
open MeasureTheory
open scoped Pointwise
open SumProduct
open scoped Classical
open MeasureTheory NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
namespace SumProduct
theorem _root_.solution (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (r : ℝ) (hr : 0 ≤ r) :
    (2 * r) ^ (Module.finrank ℚ K - 1) / Real.sqrt (Module.finrank ℚ K)
        ≤ (volume (unitBox K r)).toReal ∧
      (volume (unitBox K r)).toReal
        ≤ 5 * (2 * r) ^ (Module.finrank ℚ K - 1) / Real.sqrt (Module.finrank ℚ K) :=
  hensley_unitBox_volume_proof K r hr
end SumProduct
