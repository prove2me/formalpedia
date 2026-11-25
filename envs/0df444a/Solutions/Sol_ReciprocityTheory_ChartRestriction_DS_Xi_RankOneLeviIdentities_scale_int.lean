-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.scale_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:19:07.039013+00:00
-- url     : https://prove2.me/submissions/2c28e0d1-b682-4271-85ad-34bc548054dc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ScaleInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
namespace ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {r : ℝ}
    (hr : (Module.finrank ℝ E : ℝ) < r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : ℝ, 0 < a → 0 < b →
      ∫⁻ x, ENNReal.ofReal ((a + b * ‖x‖) ^ (-r)) ∂μ ≤
        ENNReal.ofReal (K * a ^ (-r) * (a / b) ^ (Module.finrank ℝ E : ℝ)) := by
  have hg := integrable_one_add_norm (μ := μ) hr
  refine ⟨∫ x, (1 + ‖x‖) ^ (-r) ∂μ, integral_nonneg fun x => by positivity, fun a b ha hb => ?_⟩
  have ht : 0 < a / b := div_pos ha hb
  have ha' := ha.ne'
  have hb' := hb.ne'
  have hpt : ∀ x : E, (a + b * ‖x‖) ^ (-r) = a ^ (-r) * (1 + ‖(a / b)⁻¹ • x‖) ^ (-r) := by
    intro x
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le),
      ← Real.mul_rpow ha.le (by positivity : (0 : ℝ) ≤ 1 + (a / b)⁻¹ * ‖x‖)]
    congr 1
    first | (field_simp; done) | (field_simp; ring)
  have hF : Integrable (fun x => a ^ (-r) * (1 + ‖(a / b)⁻¹ • x‖) ^ (-r)) μ :=
    (hg.comp_smul (inv_ne_zero ht.ne')).const_mul (a ^ (-r))
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hF (Filter.Eventually.of_forall fun x =>
    mul_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg (by positivity) _))]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_const_mul, Measure.integral_comp_smul (μ := μ) (f := fun y => (1 + ‖y‖) ^ (-r)) (R := (a / b)⁻¹),
    smul_eq_mul, inv_pow, inv_inv, abs_of_pos (pow_pos ht _), Real.rpow_natCast]
  exact le_of_eq (by ring)
end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
