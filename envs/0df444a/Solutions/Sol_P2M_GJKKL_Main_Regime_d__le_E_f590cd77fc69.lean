-- Prove2me | solution 1 for P2M_GJKKL_Main_Regime_d__le_E_f590cd77fc69
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:17:17.285417+00:00
-- url     : https://prove2.me/submissions/26c9d501-4235-40a0-b688-0f78934f2f7f

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Main_Regime_rp_le

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
namespace GJKKL.Main.Regime
theorem _root_.solution : d ^ (1 - ε) ≤ d ^ (1 - ε / 8) := R.rp_le (by linarith [R.ε_pos])
end GJKKL.Main.Regime
