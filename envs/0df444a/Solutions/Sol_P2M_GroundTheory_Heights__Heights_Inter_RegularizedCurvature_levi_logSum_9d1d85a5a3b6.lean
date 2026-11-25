-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_logSum_9d1d85a5a3b6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:42:03.700113+00:00
-- url     : https://prove2.me/submissions/76ee7345-dea8-4f40-87c7-e815745286b7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegularizedCurvature
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_le_of_le_fa7336628a43
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_const_1f6796170df7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_log_norm_pluriharmonic_feca3f777c61
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_log_sum_ineq_d7f2075680f7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open GroundTheory.Heights₂.Heights.Inter.RegularizedCurvature
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian
set_option linter.unusedSectionVars false
variable {J : Type} [Fintype J]
namespace GroundTheory.Heights₂.Heights.Inter.RegularizedCurvature
theorem _root_.solution {h : (J → ℂ) → ℝ} {T : (J → ℂ) → ℂ} {Φ : (J → ℂ) → ℝ} {z : J → ℂ} {ε : ℝ}
    (hφ : ContDiffAt ℝ 2 (fun y => Real.log (h y)) z) (hpos : ∀ᶠ y in 𝓝 z, 0 < h y)
    (hT : AnalyticAt ℂ T z) (hε : 0 < ε) (hΦ : ContDiffAt ℝ 2 Φ z)
    (hform : ∀ y, Φ y = Real.log (h y) + Real.log ((‖T y‖ / h y) ^ 2 + ε) / 2) (w : J → ℂ) :
    ∃ μ : ℝ, 0 ≤ μ ∧ μ ≤ 1 ∧
      μ * ReciprocityTheory.AnForm.levi (fun y => Real.log (h y)) z w ≤ ReciprocityTheory.AnForm.levi Φ z w := by
  have hc1 : ContDiffAt ℝ 2 (fun _ : J → ℂ => (1 : ℝ)) z := contDiffAt_const
  by_cases h0 : T z = 0
  ·
    refine ⟨1, zero_le_one, le_rfl, ?_⟩
    have hψ : ContDiffAt ℝ 2 (fun y => Real.log (h y) + Real.log ε / 2 * (fun _ : J → ℂ => (1 : ℝ)) y) z :=
      hφ.add (contDiffAt_const.mul hc1)
    have hle := levi_le_of_le hΦ hψ (Eventually.of_forall fun y => by
        rw [hform y]
        have : Real.log ε ≤ Real.log ((‖T y‖ / h y) ^ 2 + ε) :=
          Real.log_le_log hε (by nlinarith [sq_nonneg (‖T y‖ / h y)])
        linarith) (by rw [hform z, h0]; simp) w
    rw [ReciprocityTheory.AnForm.levi_add_smul _ hφ hc1 w, levi_const] at hle
    linarith
  ·
    obtain ⟨hg1, hlg⟩ := log_norm_pluriharmonic hT h0 w
    have hz : 0 < h z := hpos.self_of_nhds
    set x0 : ℝ := (‖T z‖ / h z) ^ 2 with hx0
    have hx0p : 0 < x0 := pow_pos (div_pos (norm_pos_iff.mpr h0) hz) 2
    have hS : 0 < x0 + ε := by linarith
    set l : ℝ := x0 / (x0 + ε) with hl
    set m : ℝ := ε / (x0 + ε) with hm
    have hlm : l + m = 1 := by rw [hl, hm, ← add_div, div_self hS.ne']
    have hm0 : 0 < m := div_pos hε hS
    have hl0 : 0 < l := div_pos hx0p hS
    set c : ℝ := Φ z - m * Real.log (h z) - l * Real.log ‖T z‖ with hc
    refine ⟨m, hm0.le, by linarith, ?_⟩
    have hA : ContDiffAt ℝ 2 (fun y => c + m * Real.log (h y)) z := contDiffAt_const.add (contDiffAt_const.mul hφ)
    have hψ : ContDiffAt ℝ 2 (fun y => (c + m * Real.log (h y)) + l * Real.log ‖T y‖) z :=
      hA.add (contDiffAt_const.mul hg1)

    have hid : ∀ y, 0 < h y → T y ≠ 0 → Φ y - m * Real.log (h y) - l * Real.log ‖T y‖ =
        (Real.log ((‖T y‖ / h y) ^ 2 + ε) - l * Real.log ((‖T y‖ / h y) ^ 2)) / 2 := by
      intro y hy hTy
      rw [hform y, Real.log_pow, Real.log_div (norm_ne_zero_iff.mpr hTy) hy.ne']
      have : m = 1 - l := by linarith
      rw [this]
      push_cast
      ring
    have hle := levi_le_of_le hΦ hψ (by
        filter_upwards [hpos, hT.continuousAt.eventually_ne h0] with y hy hTy
        have hxy : 0 < (‖T y‖ / h y) ^ 2 := pow_pos (div_pos (norm_pos_iff.mpr hTy) hy) 2
        have e1 := hid y hy hTy
        have e2 := hid z hz h0
        have key := log_sum_ineq hxy hx0p hε
        rw [← hx0] at e2
        rw [hc]
        linarith) (by rw [hc]; ring) w
    have hlevi : ReciprocityTheory.AnForm.levi (fun y => (c + m * Real.log (h y)) + l * Real.log ‖T y‖) z w =
        m * ReciprocityTheory.AnForm.levi (fun y => Real.log (h y)) z w := by
      rw [ReciprocityTheory.AnForm.levi_add_smul (f := fun y => c + m * Real.log (h y)) l hA hg1 w, hlg,
        ReciprocityTheory.AnForm.levi_add_smul (f := fun _ => c) m contDiffAt_const hφ w, levi_const]
      ring
    rw [hlevi] at hle
    exact hle
end GroundTheory.Heights₂.Heights.Inter.RegularizedCurvature
