-- Prove2me | solution 1 for ThreeSum.BandScales.bandSize_eventually_le_twice_unrounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:24:15.760245+00:00
-- url     : https://prove2.me/submissions/b8c4d158-578d-485a-b090-36f2a99a66a2

import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_Submission_ThreeSum_BandScales
import Theorems.Thm_ThreeSum_BandScales_bandDivisor_pos
import Theorems.Thm_ThreeSum_BandScales_bandSize_mul_bounds
import Theorems.Thm_ThreeSum_BandScales_unroundedBand_eventually_ge_one
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.BandScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section
namespace ThreeSum.BandScales
theorem _root_.solution :
    ∀ᶠ n : ℕ in atTop, (bandSize n : ℝ) ≤ 2 * unroundedBand n := by
  filter_upwards [unroundedBand_eventually_ge_one] with n hn
  have hD : (0 : ℝ) < bandDivisor n := by exact_mod_cast bandDivisor_pos n
  have hu : (bandDivisor n : ℝ) * bandSize n < bandRoot n + bandDivisor n := by
    exact_mod_cast (bandSize_mul_bounds n).2
  have hb : (bandSize n : ℝ) < unroundedBand n + 1 := by
    rw [unroundedBand]
    have heq : ((bandRoot n : ℝ) + bandDivisor n) / bandDivisor n =
        (bandRoot n : ℝ) / bandDivisor n + 1 := by field_simp
    rw [← heq]
    apply (lt_div_iff₀ hD).mpr
    simpa only [mul_comm] using hu
  linarith
end ThreeSum.BandScales
