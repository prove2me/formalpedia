-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.lintegral_coneFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:36:15.833848+00:00
-- url     : https://prove2.me/submissions/07c46187-3c2f-4ca7-b467-bbeb1a19ec11

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LintegralIoiOfRealMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ArchimedeanConeVolume_measurable_coneFun
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ArchimedeanConeVolume_lintegral_cylindrical
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ArchimedeanConeVolume_lintegral_plane_polar
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ArchimedeanConeVolume_lintegral_theta
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ArchimedeanConeVolume_lintegral_Ioi_ofReal_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Real
open scoped ENNReal Pointwise
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
namespace ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
theorem _root_.solution (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x : E3, coneFun G (x 0) ((x 1) ^ 2 + (x 2) ^ 2) =
      volume (Ioo (-π) π) * (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) * (Iio (1 : ℝ)).indicator 1 r) *
        ∫⁻ t in Ioo (-1 : ℝ) 1, G t := by
  have hN := measurable_coneFun hG
  rw [lintegral_cylindrical (fun q => coneFun G q.1 (q.2.1 ^ 2 + q.2.2 ^ 2))
    (hN.comp (by fun_prop : Measurable fun q : ℝ × (ℝ × ℝ) => (q.1, q.2.1 ^ 2 + q.2.2 ^ 2)))]
  have hin : ∀ z : ℝ, ∫⁻ p : ℝ × ℝ, coneFun G z (p.1 ^ 2 + p.2 ^ 2) =
      (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * coneFun G z (r ^ 2)) * volume (Ioo (-π) π) := by
    intro z
    rw [lintegral_plane_polar]
    have h : ∀ q : ℝ × ℝ, ENNReal.ofReal q.1 *
        coneFun G z ((q.1 * cos q.2) ^ 2 + (q.1 * sin q.2) ^ 2) =
        (ENNReal.ofReal q.1 * coneFun G z (q.1 ^ 2)) * (fun _ : ℝ => (1 : ℝ≥0∞)) q.2 := by
      intro q
      have : (q.1 * cos q.2) ^ 2 + (q.1 * sin q.2) ^ 2 = q.1 ^ 2 := by
        calc _ = q.1 ^ 2 * (sin q.2 ^ 2 + cos q.2 ^ 2) := by ring
          _ = q.1 ^ 2 := by rw [sin_sq_add_cos_sq, mul_one]
      rw [this, mul_one]
    simp_rw [h]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_mul
      (f := fun r : ℝ => ENNReal.ofReal r * coneFun G z (r ^ 2)) (g := fun _ : ℝ => (1 : ℝ≥0∞))
      ((by fun_prop : Measurable fun r : ℝ => ENNReal.ofReal r).mul
        (hN.comp (by fun_prop : Measurable fun r : ℝ => (z, r ^ 2)))).aemeasurable
      aemeasurable_const, lintegral_one, Measure.restrict_apply_univ]
  simp_rw [hin]
  rw [lintegral_mul_const' _ _ measure_Ioo_lt_top.ne]
  simp_rw [lintegral_Ioi_ofReal_mul]
  have hprod : ∫⁻ z : ℝ, ∫⁻ r : ℝ, ENNReal.ofReal r * coneFun G z (r ^ 2) =
      ∫⁻ q : ℝ × ℝ, ENNReal.ofReal q.2 * coneFun G q.1 (q.2 ^ 2) := by
    have hm : Measurable fun q : ℝ × ℝ => ENNReal.ofReal q.2 * coneFun G q.1 (q.2 ^ 2) :=
      (by fun_prop : Measurable fun q : ℝ × ℝ => ENNReal.ofReal q.2).mul
        (hN.comp (by fun_prop : Measurable fun q : ℝ × ℝ => (q.1, q.2 ^ 2)))
    rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
  rw [hprod, lintegral_plane_polar]
  have hset : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) := measurableSet_Ioi.prod measurableSet_Ioo
  rw [setLIntegral_congr_fun hset (g := fun q : ℝ × ℝ =>
      (ENNReal.ofReal (q.1 ^ 2) * (Iio (1 : ℝ)).indicator 1 q.1) *
        (ENNReal.ofReal (sin q.2) * G (cos q.2))) ?_]
  · rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_mul
      (f := fun r : ℝ => ENNReal.ofReal (r ^ 2) * (Iio (1 : ℝ)).indicator 1 r)
      (g := fun θ : ℝ => ENNReal.ofReal (sin θ) * G (cos θ)) (by
        refine ((by fun_prop : Measurable fun r : ℝ => ENNReal.ofReal (r ^ 2)).mul ?_).aemeasurable
        exact measurable_const.indicator measurableSet_Iio)
      ((by fun_prop : Measurable fun θ : ℝ => ENNReal.ofReal (sin θ)).mul
        (hG.comp continuous_cos.measurable)).aemeasurable, lintegral_theta]
    ring
  · rintro ⟨r, θ⟩ ⟨hr, -⟩
    simp only at hr ⊢
    have hr : 0 < r := hr
    have hs : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by
      calc _ = r ^ 2 * (sin θ ^ 2 + cos θ ^ 2) := by ring
        _ = r ^ 2 := by rw [sin_sq_add_cos_sq, mul_one]
    have e1 : ENNReal.ofReal r * ENNReal.ofReal (r * sin θ) =
        ENNReal.ofReal (r ^ 2) * ENNReal.ofReal (sin θ) := by
      rw [← ENNReal.ofReal_mul hr.le, ← ENNReal.ofReal_mul (sq_nonneg r)]
      ring_nf
    unfold coneFun
    rw [hs, Real.sqrt_sq hr.le, mul_div_cancel_left₀ _ hr.ne']
    by_cases h1 : r < 1
    · have h2 : r ^ 2 < 1 := by nlinarith
      rw [if_pos ⟨by positivity, h2⟩, indicator_of_mem (show r ∈ Iio (1 : ℝ) from h1)]
      rw [← mul_assoc, e1]
      simp only [Pi.one_apply, mul_one]
      ring
    · have h2 : ¬ r ^ 2 < 1 := by nlinarith
      rw [if_neg (fun h => h2 h.2), indicator_of_notMem (show r ∉ Iio (1 : ℝ) from h1)]
      simp
end ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
