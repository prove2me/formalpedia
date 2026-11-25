-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.tendsto_integral_gReg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:13:34.989426+00:00
-- url     : https://prove2.me/submissions/3f64cce4-c75f-462a-adeb-6b9731abc250

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Theorems.Thm_ReciprocityTheory_AnForm_A_gReg_contDiff
import Theorems.Thm_ReciprocityTheory_AnForm_A_ae_coord_ne_zero
import Theorems.Thm_ReciprocityTheory_AnForm_A_gReg_abs_le
import Theorems.Thm_ReciprocityTheory_AnForm_A_tendsto_gReg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {n : ℕ} (i : Fin (n + 1)) (F : (Fin (n + 1) → ℂ) → ℝ) (hF : Continuous F)
    (hFc : HasCompactSupport F)
    (hlog : LocallyIntegrable (fun z : Fin (n + 1) → ℂ => Real.log ‖z i‖) volume) :
    Tendsto (fun k : ℕ => ∫ z, gReg (1 / ((k : ℝ) + 1)) (z i) * F z) atTop
      (𝓝 (∫ z, Real.log ‖z i‖ * F z)) := by
  have hε0 : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hε1 : ∀ k : ℕ, 1 / ((k : ℝ) + 1) ≤ 1 := fun k => by
    rw [div_le_one (by positivity)]; have := k.cast_nonneg (α := ℝ); linarith
  refine tendsto_integral_of_dominated_convergence
    (fun z => |Real.log ‖z i‖| * |F z| + (1 / 2) * Real.log (‖z i‖ ^ 2 + 1) * |F z|)
    (fun k => (((gReg_contDiff (hε0 k) (m := 0)).continuous.comp (continuous_apply i)).mul
      hF).aestronglyMeasurable) ?_ ?_ ?_
  · refine Integrable.add ?_ ?_
    · have := (hlog.integrable_smul_left_of_hasCompactSupport hF hFc).abs
      refine this.congr (Eventually.of_forall fun z => ?_)
      simp only [smul_eq_mul, abs_mul]; ring
    · refine Continuous.integrable_of_hasCompactSupport ?_ ?_
      · have hc : Continuous (fun z : Fin (n + 1) → ℂ => Real.log (‖z i‖ ^ 2 + 1)) :=
          Continuous.log (by fun_prop) fun z =>
            (add_pos_of_nonneg_of_pos (sq_nonneg _) one_pos).ne'
        exact (continuous_const.mul hc).mul hF.abs
      · exact hFc.abs.mul_left
  · intro k
    filter_upwards [ae_coord_ne_zero i] with z hz
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, ← add_mul]
    exact mul_le_mul_of_nonneg_right (gReg_abs_le (hε0 k) (hε1 k) hz) (abs_nonneg _)
  · filter_upwards [ae_coord_ne_zero i] with z hz
    exact (tendsto_gReg hz).mul_const _
end ReciprocityTheory.AnForm.A
