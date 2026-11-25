-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_smooth_uFun_509cc27a5950
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:12:19.931351+00:00
-- url     : https://prove2.me/submissions/43af69a1-6060-402a-ab81-6c8676be1f28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotMassEqGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotMassEq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_sqSum_pos_28c025ccad4a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_projPot_eq_9342cb7a07b6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_isPotential_multiprojPot_8c77fb2c6d01
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_lift_analyticAt_64b6a8ed765d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_proj_analyticAt_4674083765d3
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open scoped ContDiff
open GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)}
namespace GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
theorem _root_.solution (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {V : Set R.X}
    {BV : FinHolAtlas n V} (hH : HoloMap BV R.A Subtype.val)
    (hΨ : ∀ x ∈ V, Ψ (segre (R.lift x x)) ≠ 0) : BV.Smooth (uFun R Ψ V) := by
  intro j t ht
  set x : V := (BV.chart j).symm t with hx_def
  have hxs : x ∈ (BV.chart j).source := (BV.chart j).map_target ht.1
  have htx : BV.chart j x = t := (BV.chart j).right_inv ht.1
  have hF := ProjRegular.proj_analyticAt Ψ hH x hxs
  have hU := (ProjRegular.lift_analyticAt hH x hxs).2
  rw [htx] at hF hU

  have hp : ContDiffAt ℝ ∞ (fun t' => (projPot R Ψ V).φ x ((BV.chart j).symm t')) t := by
    have hsq : ContDiffAt ℝ ∞ (fun t' => ∑ l, ‖Ψ (segre (R.lift x.1 ((BV.chart j).symm t').1)) l‖ ^ 2) t :=
      ContDiffAt.sum fun l _ =>
        (((analyticAt_pi_iff.1 hF l).contDiffAt).restrict_scalars ℝ).norm_sq ℝ
    have hne : ∑ l, ‖Ψ (segre (R.lift x.1 ((BV.chart j).symm t).1)) l‖ ^ 2 ≠ 0 :=
      (sqSum_pos (hΨ x.1 x.2)).ne'
    exact hsq.log hne

  have hm : ContDiffAt ℝ ∞ (fun t' => (multiprojPot R V).φ x ((BV.chart j).symm t')) t :=
    ((isPotential_multiprojPot hH).1 x j).contDiffAt
      (((BV.chart j).isOpen_inter_preimage_symm ((R.isOpen_U x.1).preimage
        continuous_subtype_val)).mem_nhds ⟨ht.1, R.mem_U x.1⟩)
  refine ((hp.sub hm).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hU] with t' ht'
  have := projPot_eq Ψ x ((BV.chart j).symm t') ht' (hΨ _ ((BV.chart j).symm t').2)
  simp only [Function.comp_apply]
  linarith
end GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
