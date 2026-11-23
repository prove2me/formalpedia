-- Prove2me | solution 1 for P2M_Formalism_FX_LFunctionPartialSum_norm_cpow_sub_le__cd1d42d75e80
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:13.358802+00:00
-- url     : https://prove2.me/submissions/e7c35ef4-9c87-452e-b86b-cd824087d3ce

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_cpow_sub_eq_integral
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_norm_integral_le
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_integral_rpow_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.FX
open Formalism.FX.LFunctionPartialSum
namespace Formalism.FX.LFunctionPartialSum
theorem _root_.solution {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 0 < s.re) :
    ‖(x : ℂ) ^ (-s) - ((x + 1 : ℝ) : ℂ) ^ (-s)‖ ≤ ‖s‖ * x ^ (-s.re - 1) := by
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; exact lt_irrefl 0 hs
  rw [cpow_sub_eq_integral hx hs0, norm_mul]
  exact mul_le_mul_of_nonneg_left ((norm_integral_le hx s).trans (integral_rpow_le hx hs)) (norm_nonneg _)
end Formalism.FX.LFunctionPartialSum
