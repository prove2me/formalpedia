-- Prove2me | solution 1 for ThreeSum.BandScales.bandSize_mul_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:10:56.049034+00:00
-- url     : https://prove2.me/submissions/525f6fb1-7d2d-4f5c-a406-51e4205ce57a

import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_Submission_ThreeSum_BandScales
import Theorems.Thm_ThreeSum_BandScales_bandDivisor_pos
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
namespace ThreeSum.BandScales
theorem _root_.solution (n : ℕ) :
    bandRoot n ≤ bandDivisor n * bandSize n ∧
      bandDivisor n * bandSize n < bandRoot n + bandDivisor n := by
  constructor
  · exact (ceilDiv_le_iff_le_mul (a := bandDivisor n) (b := bandRoot n)
      (c := bandSize n) (bandDivisor_pos n)).mp le_rfl
  · have h := Nat.div_mul_le_self (bandRoot n + bandDivisor n - 1) (bandDivisor n)
    simp only [bandSize, Nat.ceilDiv_eq_add_pred_div]
    rw [Nat.mul_comm (bandDivisor n)]
    have hpos := bandDivisor_pos n
    omega
end ThreeSum.BandScales
