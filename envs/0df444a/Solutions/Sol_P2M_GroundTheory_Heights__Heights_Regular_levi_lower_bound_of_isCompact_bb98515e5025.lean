-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_levi_lower_bound_of_isCompact_bb98515e5025
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:49:38.147724+00:00
-- url     : https://prove2.me/submissions/df13b414-e1e4-4fc6-be78-87ea2533cee7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PCutoffs
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_chartPush_eq_zero
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_contDiffOn_compat
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_isCompact_symm_image
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_smooth_chartPush
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Set Filter Topology
open scoped ContDiff Manifold
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm.M.PLAux (chartPush chartPush_eq_zero isCompact_symm_image smooth_chartPush
  contDiffOn_compat)
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution {D : ℕ} {f : (Fin D → ℂ) → ℝ} {U K : Set (Fin D → ℂ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ w, -C * ‖w‖ ^ 2 ≤ levi f y w := by
  have hS : IsCompact (K ×ˢ sphere (0 : Fin D → ℂ) 1) := hK.prod (isCompact_sphere 0 1)
  have hc : ContinuousOn (fun p : (Fin D → ℂ) × (Fin D → ℂ) => levi f p.1 p.2)
      (K ×ˢ sphere (0 : Fin D → ℂ) 1) :=
    (ReciprocityTheory.AnForm.continuousOn_levi hU hf).mono (prod_mono hKU (subset_univ _))
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, fun y hy w => ?_⟩
  by_cases hw : w = 0
  · subst hw
    simp [ReciprocityTheory.AnForm.levi_zero]
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hu : ‖‖w‖⁻¹ • w‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn.ne']
  have hb := hC (y, ‖w‖⁻¹ • w) ⟨hy, by simpa using hu⟩
  have hb' : -max C 0 ≤ levi f y (‖w‖⁻¹ • w) := by
    have := (abs_le.1 (Real.norm_eq_abs _ ▸ hb)).1
    linarith [le_max_left C 0]
  have hw' : w = ‖w‖ • (‖w‖⁻¹ • w) := by
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  rw [hw', ReciprocityTheory.AnForm.levi_smul_dir]
  have h2 : 0 ≤ ‖w‖ ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hb' h2
  have hnn : ‖‖w‖ • (‖w‖⁻¹ • w)‖ = ‖w‖ := by rw [← hw']
  rw [hnn]
  linarith
end GroundTheory.Heights₂.Heights.Regular
