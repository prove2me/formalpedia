-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_levi_bound_compact_c78187bb777a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:58:58.382868+00:00
-- url     : https://prove2.me/submissions/b8ea065f-90bb-4b99-8288-86b7fa8dd696

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTorusInvLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PTorusInvLevi
import Theorems.Thm_ReciprocityTheory_AnForm_continuousOn_levi
import Theorems.Thm_ReciprocityTheory_AnForm_levi_smul_dir
import Theorems.Thm_ReciprocityTheory_AnForm_levi_zero


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
variable {J : Type} [Fintype J]
namespace GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi
theorem _root_.solution {φ : (J → ℂ) → ℝ} {U Q : Set (J → ℂ)} (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U)
    (hQ : IsCompact Q) (hQU : Q ⊆ U) :
    ∃ M, 0 ≤ M ∧ ∀ x ∈ Q, ∀ v, |ReciprocityTheory.AnForm.levi φ x v| ≤ M * (‖v‖ * ‖v‖) := by
  have hc := ReciprocityTheory.AnForm.continuousOn_levi hU hφ
  have hK : IsCompact (Q ×ˢ Metric.sphere (0 : J → ℂ) 1) := hQ.prod (isCompact_sphere 0 1)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (hc.mono (Set.prod_mono hQU (Set.subset_univ _)))
  refine ⟨max M 0, le_max_right _ _, fun x hx v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp [ReciprocityTheory.AnForm.levi_zero]
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  set v' : J → ℂ := (‖v‖⁻¹ : ℝ) • v with hv'def
  have hv' : v = (‖v‖ : ℝ) • v' := by
    rw [hv'def, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have hv'n : ‖v'‖ = 1 := by
    rw [hv'def, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn.ne']
  have hb : |ReciprocityTheory.AnForm.levi φ x v'| ≤ M := by
    simpa [Real.norm_eq_abs] using hM (x, v') ⟨hx, mem_sphere_zero_iff_norm.2 hv'n⟩
  calc |ReciprocityTheory.AnForm.levi φ x v| = |ReciprocityTheory.AnForm.levi φ x ((‖v‖ : ℝ) • v')| := by rw [← hv']
    _ = ‖v‖ ^ 2 * |ReciprocityTheory.AnForm.levi φ x v'| := by
      rw [ReciprocityTheory.AnForm.levi_smul_dir, abs_mul, abs_of_nonneg (sq_nonneg _)]
    _ ≤ ‖v‖ ^ 2 * max M 0 := by gcongr; exact hb.trans (le_max_left _ _)
    _ = _ := by ring
end GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi
