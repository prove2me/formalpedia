-- Prove2me | solution 1 for P2M_FixedOrderFactor_tendsto_muAvg__0f3103de6ec7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:48.010913+00:00
-- url     : https://prove2.me/submissions/4616fb10-43bc-4fa9-b938-ffea628d3678

module
public import Definitions.Def_FixedOrderFactor_Euler
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Model
public import Theorems.Thm_P2M_FixedOrderFactor_muAvg_eq__11fccbbf11a9


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {x : ℝ} (hx : |x| < 1) :
    Tendsto (fun r => muAvg r x) atTop (𝓝 (1 / (1 - x ^ 2))) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hx
  have hx2 : (1 : ℝ) - x ^ 2 ≠ 0 := by
    have : x ^ 2 < 1 := by
      have := sq_abs x; nlinarith [abs_nonneg x]
    linarith
  have hlim : Tendsto (fun r : ℕ => (1 + x ^ r) / ((1 - x ^ 2) * (1 - x ^ r))) atTop
      (𝓝 ((1 + 0) / ((1 - x ^ 2) * (1 - 0)))) := by
    refine ((tendsto_const_nhds.add hp)).div (tendsto_const_nhds.mul (tendsto_const_nhds.sub hp)) ?_
    simpa using hx2
  simp only [add_zero, sub_zero, mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  exact (muAvg_eq' hr hx).symm
end FixedOrderFactor
