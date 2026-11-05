-- Prove2me | solution 1 for PhysicalCostTransfer.uniformConstant_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/3429e53e-6971-415e-a9bb-68de762287d5

import Definitions.Def_SelectedFloorTransfer
import Definitions.Def_PhysicalCostTransfer

set_option autoImplicit true
open PhysicalCostTransfer
open scoped BigOperators
namespace PhysicalCostTransfer
theorem _root_.solution (B C γ : ℝ) (hγ : γ < 1) : 0 ≤ uniformConstant B C γ := by
  unfold uniformConstant
  exact add_nonneg (le_max_left _ _) (div_nonneg (abs_nonneg _) (by linarith))
end PhysicalCostTransfer
