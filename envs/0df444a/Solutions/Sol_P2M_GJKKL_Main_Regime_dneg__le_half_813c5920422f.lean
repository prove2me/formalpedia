-- Prove2me | solution 1 for P2M_GJKKL_Main_Regime_dneg__le_half_813c5920422f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:18:09.303116+00:00
-- url     : https://prove2.me/submissions/81333fcb-d9b2-4ba9-93b8-c473f57e6d12

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Main_Regime_d_pos
public import Theorems.Thm_P2M_GJKKL_Main_Regime_d__ge_two_14571f3b3df4

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
namespace GJKKL.Main.Regime
theorem _root_.solution : d ^ (-ε) ≤ 1 / 2 := by
  rw [rpow_neg R.d_pos.le, one_div]
  exact inv_anti₀ (by norm_num) R.dε_ge_two
end GJKKL.Main.Regime
