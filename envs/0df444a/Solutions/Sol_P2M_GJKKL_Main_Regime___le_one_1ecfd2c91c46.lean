-- Prove2me | solution 1 for P2M_GJKKL_Main_Regime___le_one_1ecfd2c91c46
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:57.203082+00:00
-- url     : https://prove2.me/submissions/f61c465d-28db-4b50-8448-5dff4d805e8a

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Main_Regime_k_ge

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
namespace GJKKL.Main.Regime
theorem _root_.solution : ε ≤ 1 := by
  have hk := R.k_ge
  have h256 : (1 : ℝ) ≤ 64 * (k : ℝ) ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_left h256 R.ε_pos.le
  linarith [R.ε_small]
end GJKKL.Main.Regime
