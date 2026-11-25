-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_levi_logBlock_115b2b2cbad8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:23:16.490266+00:00
-- url     : https://prove2.me/submissions/51a46db8-09c1-4342-bb34-a3da390f9bcf

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_FsMetricFinIsSemipositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotDensLevi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_blockCLM_apply_a12544bdf5b0
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fsLp_ne_zero

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
theorem _root_.solution (k : K) {z : (Σ k, ι k) → ℂ} (hz : blockCLM k z ≠ 0)
    (v : (Σ k, ι k) → ℂ) :
    levi (fun y : (Σ k, ι k) → ℂ => Real.log (∑ i, ‖y ⟨k, i⟩‖ ^ 2)) z v =
      2 * leviForm (fun w => Real.log ((fsMetric (ι k)).ρ w)) (blockCLM k z) (blockCLM k v) := by
  have hne : fsLp (ι k) (blockCLM k z) ≠ 0 := fsLp_ne_zero hz
  have hg : ContDiffAt ℝ 2 (fun w : ι k → ℂ => Real.log ((fsMetric (ι k)).ρ w)) (blockCLM k z) :=
    ((contDiffAt_norm ℂ hne).comp _ (fsLp (ι k)).contDiff.contDiffAt).log
      (norm_ne_zero_iff.2 hne)
  have e : (fun y : (Σ k, ι k) → ℂ => Real.log (∑ i, ‖y ⟨k, i⟩‖ ^ 2)) =
      (fun w => (fun _ => (0 : ℝ)) w + 2 * Real.log ((fsMetric (ι k)).ρ w)) ∘ blockCLM k := by
    funext y
    have hs : ∑ i, ‖y ⟨k, i⟩‖ ^ 2 = ‖fsLp (ι k) (blockCLM k y)‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      rfl
    simp only [Function.comp_apply, zero_add]
    rw [hs, Real.log_pow]
    push_cast
    rfl
  rw [e, levi_comp v ((blockCLM k).analyticAt z)
      (contDiffAt_const.add (contDiffAt_const.mul hg)), (blockCLM k).fderiv,
    levi_add_smul 2 contDiffAt_const hg]
  have h0 : levi (fun _ : ι k → ℂ => (0 : ℝ)) (blockCLM k z) (blockCLM k v) = 0 := by
    unfold levi; simp
  rw [h0, zero_add]
  rfl
end GroundTheory.Heights₂.Heights.Targets.ProjPotDens
