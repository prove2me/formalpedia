-- Prove2me | solution 1 for ThreeSum.MassScales.nat_log_rate_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:15:00.128427+00:00
-- url     : https://prove2.me/submissions/cba80220-0637-4958-8dde-b6627a69f3ac

import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Definitions.Def_Submission_ThreeSum_MassScales
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Switch_mem_candidates
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.Switch.mem_candidates



set_option autoImplicit false
open ThreeSum ThreeSum.MassScales
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.CostLedger ThreeSum.HierarchyScales
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace ThreeSum.MassScales
theorem _root_.solution {f g : ℕ → ℕ} {a b : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a))
    (hg : Tendsto (fun n : ℕ => Real.log (g n : ℝ) / Real.log n) atTop (𝓝 b))
    (hp : ∀ᶠ n : ℕ in atTop, 0 < f n ∧ 0 < g n) :
    Tendsto (fun n : ℕ => Real.log ((f n * g n : ℕ) : ℝ) / Real.log n) atTop (𝓝 (a + b)) := by
  apply (hf.add hg).congr'
  filter_upwards [hp] with n hn
  have hfR : (f n : ℝ) ≠ 0 := by exact_mod_cast hn.1.ne'
  have hgR : (g n : ℝ) ≠ 0 := by exact_mod_cast hn.2.ne'
  simp only [Nat.cast_mul, Real.log_mul hfR hgR, add_div]
end ThreeSum.MassScales
