-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.GreenFunction.integrableOn_log_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:26.111543+00:00
-- url     : https://prove2.me/submissions/c3147c00-f2bf-4873-97d5-6e8ef21054a2

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Filter Topology InnerProductSpace intervalIntegral
open scoped Laplacian
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.GreenFunction
noncomputable section
namespace ReciprocityTheory.AnForm.A.GreenFunction
theorem _root_.solution {P : ℝ × ℝ → ℝ} (hP : Continuous P) {R : ℝ} (hR0 : 0 < R)
    (hz : ∀ p : ℝ × ℝ, R < p.1 → P p = 0) :
    IntegrableOn (fun p : ℝ × ℝ => Real.log p.1 * P p) (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi) := by
  have hpi := Real.pi_pos
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Icc 0 R ×ˢ Icc (-Real.pi) Real.pi)).exists_bound_of_continuousOn hP.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _)
    (hC (0, 0) ⟨⟨le_rfl, hR0.le⟩, ⟨by linarith, by linarith⟩⟩)
  have hg : IntegrableOn (fun p : ℝ × ℝ =>
      C * (Ioc 0 R).indicator (fun r => ‖Real.log r‖) p.1 * (1 : ℝ))
      (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    have h1 : Integrable (fun r : ℝ => C * (Ioc 0 R).indicator (fun r => ‖Real.log r‖) r)
        (volume.restrict (Ioi 0)) := by
      apply Integrable.const_mul
      apply Integrable.mono_measure _ Measure.restrict_le_self
      rw [integrable_indicator_iff measurableSet_Ioc]
      exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR0.le).1 intervalIntegrable_log').norm
    have h2 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioo (-Real.pi) Real.pi)) :=
      integrableOn_const (by simp)
    exact Integrable.mul_prod (f := fun r : ℝ => C * (Ioc 0 R).indicator (fun r => ‖Real.log r‖) r)
      (g := fun _ : ℝ => (1 : ℝ)) h1 h2
  refine hg.mono' ((Real.measurable_log.comp measurable_fst).mul hP.measurable).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
  rcases le_or_gt p.1 R with h | h
  · have h1 : p.1 ∈ Ioc 0 R := ⟨hp.1, h⟩
    rw [indicator_of_mem h1, mul_one, norm_mul, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC p ⟨⟨le_of_lt hp.1, h⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩)
      (norm_nonneg _)
  · rw [hz p h, mul_zero, norm_zero]
    exact mul_nonneg (mul_nonneg hC0 (indicator_nonneg (fun _ _ => norm_nonneg _) _)) zero_le_one
end ReciprocityTheory.AnForm.A.GreenFunction
