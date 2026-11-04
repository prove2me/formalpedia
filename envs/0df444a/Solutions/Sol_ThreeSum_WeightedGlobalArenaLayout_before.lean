-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaLayout.before
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:28:49.829421+00:00
-- url     : https://prove2.me/submissions/20c3e9e7-e318-46be-a4d1-85cafa6ea2e4

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_SourceCountHost
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalArenaLayout
namespace ThreeSum.WeightedGlobalArenaLayout
theorem _root_.solution {free C i j len : ℕ} (hij : i<j) (hlen : len≤C) :
    addr free C i+len≤addr free C j := by
  have hm := Nat.mul_le_mul_right C (show i+1≤j by omega)
  rw [Nat.add_mul,Nat.one_mul] at hm
  unfold addr
  omega
end ThreeSum.WeightedGlobalArenaLayout
