-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_levi_Phi_d5cfcffc1145
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:23:11.253172+00:00
-- url     : https://prove2.me/submissions/554d5703-c49a-4e5f-811b-7e476dd7a0f0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTorusInvLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PTorusInvLevi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_log_rho_eq_phi_a87fea3648ce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_levi_add_sum_b89c89512e17
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_contDiffAt_phi_ce22939b8b91
import Theorems.Thm_ReciprocityTheory_AnForm_levi_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi
theorem _root_.solution {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (w : (Σ k, ι k) → ℂ) :
    leviForm (fun y => ∑ k, Real.log ((fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩))) z w =
      ∑ k, leviForm phi (blk k z) (blk k w) := by
  have hS : ∀ k, sqSum (blk k z) ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hz k
    refine (lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hi) 2) ?_).ne'
    exact Finset.single_le_sum (f := fun j => ‖blk k z j‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
  have hf : ∀ k, ContDiffAt ℝ 2 (phi ∘ blk (ι := ι) k) z := fun k =>
    (contDiffAt_phi (hS k)).comp z ((blk (ι := ι) k).restrictScalars ℝ).contDiff.contDiffAt
  have hfun : (fun y => ∑ k, Real.log ((fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩))) =
      fun y => (fun _ => (0 : ℝ)) y + ∑ k ∈ Finset.univ, (fun _ => (1 : ℝ)) k * (phi ∘ blk (ι := ι) k) y := by
    funext y
    simp only [zero_add, one_mul, Function.comp_apply]
    exact Finset.sum_congr rfl fun k _ => log_rho_eq_phi _
  have h := (levi_add_sum (fun _ => (0 : ℝ)) (fun k => phi ∘ blk (ι := ι) k) (fun _ => 1)
    contDiffAt_const hf w Finset.univ).2
  show ReciprocityTheory.AnForm.levi _ z w = _
  rw [hfun, h]
  have h0 : ReciprocityTheory.AnForm.levi (fun _ : (Σ k, ι k) → ℂ => (0 : ℝ)) z w = 0 := by
    simp [ReciprocityTheory.AnForm.levi]
  rw [h0, zero_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [one_mul, ReciprocityTheory.AnForm.levi_comp w ((blk (ι := ι) k).analyticAt z) (contDiffAt_phi (hS k)),
    ContinuousLinearMap.fderiv]
  rfl
end GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi
