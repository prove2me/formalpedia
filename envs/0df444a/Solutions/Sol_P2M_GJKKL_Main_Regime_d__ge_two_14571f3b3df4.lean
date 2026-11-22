-- Prove2me | solution 1 for P2M_GJKKL_Main_Regime_d__ge_two_14571f3b3df4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:54:44.205274+00:00
-- url     : https://prove2.me/submissions/e6c506ab-cee2-45f1-978c-e754fac03557

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
theorem _root_.solution : 2 ≤ d ^ ε := R.h16.trans (R.rp_le (by linarith [R.ε_pos]))
end GJKKL.Main.Regime
