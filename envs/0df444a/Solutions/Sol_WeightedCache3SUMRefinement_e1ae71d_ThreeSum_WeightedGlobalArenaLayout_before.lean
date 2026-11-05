-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaLayout.before
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:23:23.959509+00:00
-- url     : https://prove2.me/submissions/839cf75a-6d0e-4b1e-a121-179b3d4e484f

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_SourceCountHost
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLayout

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaLayout
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaLayout
theorem _root_.solution {free C i j len : ℕ} (hij : i<j) (hlen : len≤C) :
    addr free C i+len≤addr free C j := by
  have hm := Nat.mul_le_mul_right C (show i+1≤j by omega)
  rw [Nat.add_mul,Nat.one_mul] at hm
  unfold addr
  omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaLayout
