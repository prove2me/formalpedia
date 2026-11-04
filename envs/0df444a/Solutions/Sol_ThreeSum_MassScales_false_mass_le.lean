-- Prove2me | solution 1 for ThreeSum.MassScales.false_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:15:03.872286+00:00
-- url     : https://prove2.me/submissions/a6b3039a-ddcd-488d-aa1c-e854da54650c

import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Definitions.Def_Submission_ThreeSum_MassScales
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Scales_radix_pos
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
theorem _root_.solution {n k P H H1 : ℕ}
    (hscore : P * H ≤ scoreLoss k n * H1)
    (hinit : H1 ≤ candidateCount n * rawTripleBound n)
    (hmod : radix n ≤ primeLoss radix n * P) :
    (H : ℝ) ≤ falseMajorant k n := by
  have hbound : H * radix n ≤ falseNumerator k n := by
    calc
      H * radix n ≤ primeLoss radix n * (P * H) := by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using Nat.mul_le_mul_left H hmod
      _ ≤ primeLoss radix n * (scoreLoss k n * H1) := Nat.mul_le_mul_left _ hscore
      _ ≤ primeLoss radix n * (scoreLoss k n * (candidateCount n * rawTripleBound n)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hinit)
      _ = falseNumerator k n := by unfold falseNumerator; ring
  rw [falseMajorant, le_div_iff₀ (show (0 : ℝ) < radix n by exact_mod_cast radix_pos n)]
  exact_mod_cast hbound
end ThreeSum.MassScales
