-- Prove2me | solution 1 for ThreeSum.StageBounds.PowerBound.add_same_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:47:49.180205+00:00
-- url     : https://prove2.me/submissions/1e6a0042-d7bd-4db6-82dd-0975c6fc85bd

import Definitions.Def_Submission_ThreeSum_MassScales
import Definitions.Def_Submission_ThreeSum_StageBounds
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_const
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Switch_mem_candidates
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.Switch.mem_candidates



set_option autoImplicit false
open ThreeSum ThreeSum.StageBounds
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
open ThreeSum.StageBounds.PowerBound
namespace ThreeSum.StageBounds.PowerBound
theorem _root_.solution {f g : ℕ → ℕ} {a : ℝ} (hf : PowerBound f a) (hg : PowerBound g a) :
    PowerBound (fun n => f n + g n) a := by
  intro d hd
  filter_upwards [hf (d / 2) (by linarith), hg (d / 2) (by linarith),
    (const 2) (d / 2) (by linarith), eventually_ge_atTop (1 : ℕ)] with n hfn hgn htwo hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  simp only [zero_add, Nat.cast_ofNat] at htwo
  rw [Nat.cast_add]
  calc
    _ ≤ 2 * (n : ℝ) ^ (a + d / 2) := by linarith
    _ ≤ (n : ℝ) ^ (d / 2) * (n : ℝ) ^ (a + d / 2) :=
      mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hnR.le _)
    _ = (n : ℝ) ^ (a + d) := by rw [← Real.rpow_add hnR]; congr 1; ring
end ThreeSum.StageBounds.PowerBound
