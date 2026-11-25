-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_exists_levi_lower_a1c52ccadca0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:00:17.229813+00:00
-- url     : https://prove2.me/submissions/0dfe232b-8972-4d53-ac4e-78468867988e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StChartLeviThGe
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartLeviThGe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_levi_base_indep_c0ed9c553384
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_levi_pos_compat_1b0edf5128a1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_continuousAt_levi_self_0e89eed5c63b
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_analyticAt_compat
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_contDiffOn_compat
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_AnForm_continuousOn_levi
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_comp
import Theorems.Thm_ReciprocityTheory_AnForm_levi_congr
import Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic
import Theorems.Thm_ReciprocityTheory_AnForm_levi_smul_dir
import Theorems.Thm_ReciprocityTheory_AnForm_levi_zero
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
open Filter Topology Metric
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_zero levi_smul_dir levi_add_smul
  levi_re_analytic continuousOn_levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot IsCompatChart)
open ReciprocityTheory.AnForm.M.PLAux (contDiffOn_compat analyticAt_compat)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe
variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
variable {om : LocPot X}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe
theorem _root_.solution (hpot : IsPotential A om) (hpos : IsPosPot A om)
    {ψ : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ) {K : Set X}
    (hK : IsCompact K) (hKs : K ⊆ ψ.source) :
    ∃ c : ℝ, 0 < c ∧ ∀ p ∈ K, ∀ x, p ∈ om.U x → ∀ v : Fin D → ℂ,
      c * ‖v‖ ^ 2 ≤ levi (om.φ x ∘ ψ.symm) (ψ p) v := by
  have hunit : ∀ v : Fin D → ℂ, v ≠ 0 → ‖‖v‖⁻¹ • v‖ = 1 := fun v hv => by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]
  by_cases hne : (K ×ˢ sphere (0 : Fin D → ℂ) 1).Nonempty
  · have hcont : ContinuousOn (fun q : X × (Fin D → ℂ) => levi (om.φ q.1 ∘ ψ.symm) (ψ q.1) q.2)
        (K ×ˢ sphere (0 : Fin D → ℂ) 1) := fun q hq =>
      (continuousAt_levi_self hpot hψ (hKs hq.1) q.2).continuousWithinAt
    obtain ⟨q1, hq1, hmin⟩ := (hK.prod (isCompact_sphere 0 1)).exists_isMinOn hne hcont
    have hq1v : q1.2 ≠ 0 := by
      intro h0
      have := hq1.2
      rw [mem_sphere_zero_iff_norm, h0, norm_zero] at this
      exact zero_ne_one this
    refine ⟨_, levi_pos_compat hpot hpos hψ (om.mem_U q1.1) (hKs hq1.1) hq1v, ?_⟩
    intro p hp x hx v
    rw [levi_base_indep hpot hψ hx (om.mem_U p) (hKs hp) v]
    by_cases hv : v = 0
    · subst hv; simp [levi_zero]
    have hm := isMinOn_iff.1 hmin (p, ‖v‖⁻¹ • v) ⟨hp, by rw [mem_sphere_zero_iff_norm]; exact hunit v hv⟩
    have hw : v = ‖v‖ • (‖v‖⁻¹ • v) := by
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hv), one_smul]
    have hs : levi (om.φ p ∘ ψ.symm) (ψ p) v =
        ‖v‖ ^ 2 * levi (om.φ p ∘ ψ.symm) (ψ p) (‖v‖⁻¹ • v) := by
      conv_lhs => rw [hw]
      exact levi_smul_dir _ _ _ _
    rw [hs, mul_comm]
    exact mul_le_mul_of_nonneg_left hm (sq_nonneg _)
  · refine ⟨1, one_pos, fun p hp x hx v => ?_⟩
    by_cases hv : v = 0
    · subst hv; simp [levi_zero]
    exact absurd ⟨(p, ‖v‖⁻¹ • v), hp, by rw [mem_sphere_zero_iff_norm]; exact hunit v hv⟩ hne
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe
