-- Prove2me | solution 1 for PhysicalCostTransfer.uniformConstant_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/38fc9908-96fa-4949-a02c-1824fee608b3

import Definitions.Def_SelectedFloorTransfer
import Definitions.Def_PhysicalCostTransfer

set_option autoImplicit true
open PhysicalCostTransfer
open scoped BigOperators
namespace PhysicalCostTransfer
theorem _root_.solution (B C γ : ℝ) (hγ : γ < 1) : B ≤ uniformConstant B C γ := by
  have hmax : B ≤ max 0 B := le_max_right _ _
  have hquot : 0 ≤ |C| / (1 - γ) := div_nonneg (abs_nonneg _) (by linarith)
  unfold uniformConstant
  linarith
end PhysicalCostTransfer
