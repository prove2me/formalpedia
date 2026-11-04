-- Prove2me | solution 1 for ThreeSum.StageBounds.amplifiedCoreWork_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:09:29.963591+00:00
-- url     : https://prove2.me/submissions/936a11cb-1818-4adb-a0db-bfc19118157b

import Definitions.Def_Submission_ThreeSum_MassScales
import Definitions.Def_Submission_ThreeSum_StageBounds
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mul
import Theorems.Thm_ThreeSum_StageBounds_coreWork_powerBound
import Theorems.Thm_ThreeSum_StageBounds_concreteOverhead_powerBound
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
    PowerBound (amplifiedCoreWork C W H) certificateExponent := by
  intro d hd
  have hh := ((concreteOverhead_powerBound C).mul
    (coreWork_powerBound k hW hscore hinit hmod)) d hd
  simpa only [amplifiedCoreWork, zero_add] using hh
end ThreeSum.StageBounds
