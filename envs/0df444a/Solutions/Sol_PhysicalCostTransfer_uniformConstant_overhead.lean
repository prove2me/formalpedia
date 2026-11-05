-- Prove2me | solution 1 for PhysicalCostTransfer.uniformConstant_overhead
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/0fbb435c-859d-4b41-86c4-a3b4591b157d

import Definitions.Def_SelectedFloorTransfer
import Definitions.Def_PhysicalCostTransfer

set_option autoImplicit true
open PhysicalCostTransfer
open scoped BigOperators
namespace PhysicalCostTransfer
theorem _root_.solution (B C γ : ℝ) (hγ : γ < 1) :
    C ≤ uniformConstant B C γ * (1 - γ) := by
  have hgap : 0 < 1 - γ := by linarith
  have hmax : 0 ≤ max 0 B := le_max_left _ _
  have hle : |C| / (1 - γ) ≤ uniformConstant B C γ := by unfold uniformConstant; linarith
  have h := mul_le_mul_of_nonneg_right hle hgap.le
  rw [div_mul_cancel₀ _ hgap.ne'] at h
  exact (le_abs_self C).trans h
end PhysicalCostTransfer
