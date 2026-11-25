-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_levi_fsMultiPot_e06421934b30
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:53:55.131806+00:00
-- url     : https://prove2.me/submissions/359cf65f-9dbe-45b4-bc0b-8930924f80ad

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_FsMetricFinIsSemipositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotDensLevi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_blockCLM_apply_a12544bdf5b0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_levi_finset_sum_312a038d2ebc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_levi_logBlock_115b2b2cbad8
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fsLp_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fsLp_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fsMetric_isSemipositive
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_leviForm_fsMetric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Heights₂.Heights.Targets.ProjPotDens.blockCLM_apply

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open GroundTheory.Heights₂.Heights.Targets.ProjPotDens
open ReciprocityTheory.AnForm ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets.ProjPotDens
theorem _root_.solution (p : (k : K) → ι k) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, z ⟨k, p k⟩ ≠ 0) (v : (Σ k, ι k) → ℂ) :
    ContDiffAt ℝ 2 fsMultiPot z ∧ 0 ≤ levi fsMultiPot z v ∧
      ((∀ k, v ⟨k, p k⟩ = 0) → v ≠ 0 → 0 < levi fsMultiPot z v) := by
  have hb : ∀ k, blockCLM k z ≠ 0 := fun k h => hz k (by simpa using congrFun h (p k))
  have hpos : ∀ k, 0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := fun k =>
    lt_of_lt_of_le (by have := norm_pos_iff.2 (hz k); positivity)
      (Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ (p k)))
  have hC : ∀ k ∈ (Finset.univ : Finset K),
      ContDiffAt ℝ 2 (fun y : (Σ k, ι k) → ℂ => Real.log (∑ i, ‖y ⟨k, i⟩‖ ^ 2)) z := fun k _ =>
    ((ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp
      (contDiff_apply ℝ ℂ (⟨k, i⟩ : Σ k, ι k))).contDiffAt).log (hpos k).ne'
  have hsum : levi fsMultiPot z v = ∑ k, 2 * leviForm (fun w => Real.log ((fsMetric (ι k)).ρ w))
      (blockCLM k z) (blockCLM k v) := by
    rw [show (fsMultiPot : ((Σ k, ι k) → ℂ) → ℝ) =
      fun y => ∑ k, Real.log (∑ i, ‖y ⟨k, i⟩‖ ^ 2) from rfl, levi_finset_sum _ _ hC]
    exact Finset.sum_congr rfl fun k _ => levi_logBlock k (hb k) v
  have hterm : ∀ k, 0 ≤ leviForm (fun w => Real.log ((fsMetric (ι k)).ρ w))
      (blockCLM k z) (blockCLM k v) := fun k => fsMetric_isSemipositive.2 _ (hb k) _
  have hstrict : ∀ k, v ⟨k, p k⟩ = 0 → blockCLM k v ≠ 0 →
      0 < leviForm (fun w => Real.log ((fsMetric (ι k)).ρ w)) (blockCLM k z) (blockCLM k v) := by
    intro k hv hbv
    rw [leviForm_fsMetric (hb k)]
    have hb0 : fsLp (ι k) (blockCLM k z) ≠ 0 := fsLp_ne_zero (hb k)
    have ha0 : fsLp (ι k) (blockCLM k v) ≠ 0 := fsLp_ne_zero hbv
    have hlt : ‖inner ℂ (fsLp (ι k) (blockCLM k z)) (fsLp (ι k) (blockCLM k v))‖ <
        ‖fsLp (ι k) (blockCLM k z)‖ * ‖fsLp (ι k) (blockCLM k v)‖ := by
      refine lt_of_le_of_ne (norm_inner_le_norm _ _) fun heq => ?_
      obtain ⟨r, hr, hra⟩ := (norm_inner_eq_norm_iff hb0 ha0).1 heq
      have h1 := congrArg (fun u : EuclideanSpace ℂ (ι k) => u (p k)) hra
      simp only [fsLp_apply, PiLp.toLp_apply, PiLp.smul_apply, blockCLM_apply, smul_eq_mul] at h1
      rw [hv] at h1
      exact mul_ne_zero hr (hz k) h1.symm
    apply div_pos _ (by have := norm_pos_iff.2 hb0; positivity)
    nlinarith [mul_self_lt_mul_self (norm_nonneg _) hlt, norm_nonneg (fsLp (ι k) (blockCLM k z)),
      norm_nonneg (fsLp (ι k) (blockCLM k v))]
  refine ⟨ContDiffAt.sum hC, ?_, fun hv hv0 => ?_⟩
  · rw [hsum]
    exact Finset.sum_nonneg fun k _ => mul_nonneg zero_le_two (hterm k)
  · obtain ⟨⟨k, i⟩, hq⟩ := Function.ne_iff.1 hv0
    have hbv : blockCLM k v ≠ 0 := fun h => hq (by simpa using congrFun h i)
    rw [hsum]
    exact Finset.sum_pos' (fun k _ => mul_nonneg zero_le_two (hterm k))
      ⟨k, Finset.mem_univ _, mul_pos two_pos (hstrict k (hv k) hbv)⟩
end GroundTheory.Heights₂.Heights.Targets.ProjPotDens
