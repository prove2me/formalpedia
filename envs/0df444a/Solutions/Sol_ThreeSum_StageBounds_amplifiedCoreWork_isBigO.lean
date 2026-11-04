-- Prove2me | solution 1 for ThreeSum.StageBounds.amplifiedCoreWork_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:14:42.627943+00:00
-- url     : https://prove2.me/submissions/e4f80a9d-ee95-40fb-ae5a-6b82b749255f

import Definitions.Def_Submission_ThreeSum_MassScales
import Definitions.Def_Submission_ThreeSum_StageBounds
import Theorems.Thm_ThreeSum_StageBounds_amplifiedCoreWork_eventually_target
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
namespace ThreeSum.StageBounds
theorem _root_.solution {W H P H1 : ℕ → ℕ} (C k : ℕ)
    (hW : ∀ᶠ n : ℕ in atTop, W n * radix n ≤ wantedNumerator n)
    (hscore : ∀ᶠ n : ℕ in atTop, P n * H n ≤ scoreLoss k n * H1 n)
    (hinit : ∀ᶠ n : ℕ in atTop, H1 n ≤ candidateCount n * rawTripleBound n)
    (hmod : ∀ᶠ n : ℕ in atTop, radix n ≤ primeLoss radix n * P n) :
    (fun n : ℕ => (amplifiedCoreWork C W H n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ targetExponent) := by
  apply _root_.Asymptotics.IsBigO.of_norm_eventuallyLE
  filter_upwards [amplifiedCoreWork_eventually_target C k hW hscore hinit hmod] with n hn
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (amplifiedCoreWork C W H n)),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) n) targetExponent)] using hn
end ThreeSum.StageBounds
