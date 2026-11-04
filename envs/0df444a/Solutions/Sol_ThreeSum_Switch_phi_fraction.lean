-- Prove2me | solution 1 for ThreeSum.Switch.phi_fraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:46:29.219722+00:00
-- url     : https://prove2.me/submissions/79252452-89f8-47d2-b8c4-a22cb105d3d8

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
import Theorems.Thm_ThreeSum_Switch_mem_candidates
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_PrimeDensity_mem_candidates
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices


attribute [local simp] ThreeSum.Switch.mem_candidates

set_option autoImplicit false
open ThreeSum ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0
noncomputable section
namespace ThreeSum.Switch
theorem _root_.solution {r q : ℕ} (hr : 0 < r) :
    phi ((q : ℝ) / r) = (cubicNumerator r q : ℝ) / (100 * (r : ℝ) ^ 3) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [phi, cubicNumerator, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  <;> ring
end ThreeSum.Switch
