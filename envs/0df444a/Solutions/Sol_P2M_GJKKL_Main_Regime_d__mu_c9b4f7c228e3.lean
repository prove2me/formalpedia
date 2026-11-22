-- Prove2me | solution 1 for P2M_GJKKL_Main_Regime_d__mu_c9b4f7c228e3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:55:12.762799+00:00
-- url     : https://prove2.me/submissions/5247752c-db6f-47d3-885e-7c18990636ef

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Main_Regime_rp_mul

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
namespace GJKKL.Main.Regime
theorem _root_.solution : d ^ ε * d ^ (-(ε ^ 3)) = d ^ (ε - ε ^ 3) := by
  rw [R.rp_mul, ← sub_eq_add_neg]
end GJKKL.Main.Regime
