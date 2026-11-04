-- Prove2me | solution 1 for ThreeSum.StageBounds.active_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:03:15.049115+00:00
-- url     : https://prove2.me/submissions/08938b0d-31a6-43e3-82e0-b2885dde294c

import Definitions.Def_Submission_ThreeSum_MassScales
import Definitions.Def_Submission_ThreeSum_StageBounds
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_of_rate
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mul
import Theorems.Thm_ThreeSum_StageBounds_false_powerBound
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_HierarchyScales_allQueryTerms_eventually_le
import Theorems.Thm_ThreeSum_HierarchyScales_microPartitions_subpolynomial
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Switch_mem_candidates
import Definitions.Def_WeightedCache3SUM_Alias_dc2f19a97a662b74
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
theorem _root_.solution {H P H1 : ℕ → ℕ} (k : ℕ)
    (hscore : ∀ᶠ n : ℕ in atTop, P n * H n ≤ scoreLoss k n * H1 n)
    (hinit : ∀ᶠ n : ℕ in atTop, H1 n ≤ candidateCount n * rawTripleBound n)
    (hmod : ∀ᶠ n : ℕ in atTop, radix n ≤ primeLoss radix n * P n) :
    PowerBound (activeCount H)
      (2 - epsilon * (1 / 2 - bandShift - kappa - entropyRatio * (1 + boxSaving - 2 * bandShift))) := by
  have hG : PowerBound microPartitions 0 := by
    intro d hd
    simpa only [zero_add] using microPartitions_subpolynomial hd
  have hQ : PowerBound allQueryTerms ((entropyRatio * (1 + boxSaving - 2 * bandShift)) / 5) :=
    fun _ hd => allQueryTerms_eventually_le hd
  have hh := (((false_powerBound k hscore hinit hmod).mul
    (PowerBound.of_rate representationBound_log_rate)).mul hG).mul hQ
  have heq : ((2 - (1 / 2 - bandShift) / 5) + kappa / 5 + 0) +
      (entropyRatio * (1 + boxSaving - 2 * bandShift)) / 5 =
      2 - epsilon * (1 / 2 - bandShift - kappa - entropyRatio * (1 + boxSaving - 2 * bandShift)) := by
    unfold epsilon
    ring
  rw [heq] at hh
  exact hh
end ThreeSum.StageBounds
