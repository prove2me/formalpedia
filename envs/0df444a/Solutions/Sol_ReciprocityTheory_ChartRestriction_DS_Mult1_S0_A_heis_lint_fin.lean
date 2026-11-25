-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A.heis_lint_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:26:22.478685+00:00
-- url     : https://prove2.me/submissions/5455d008-e4cf-4582-82e8-961796e655d2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_HermitianMeasures_NHeisInt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_S0_A_heis_pointwise

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Mult1 ReciprocityTheory.ChartRestriction.DS.Mult1.S0 ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
theorem _root_.solution (m : ℕ) {d : ℝ} (hd : (2 * m + 1 : ℝ) < d) :
    ∫⁻ x : (Fin m → ℂ) × ℝ, ENNReal.ofReal ((1 + ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) ^ (-(d / 2))) < ∞ := by
  have hd0 : 0 ≤ d := by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have hfin : ∫⁻ x : (Fin m → ℂ) × ℝ, ENNReal.ofReal ((1 + ‖x‖) ^ (-d)) < ⊤ := by
    haveI hC : (volume : Measure ℂ).IsAddHaarMeasure := by
      first
        | infer_instance
        | exact Complex.isAddHaarMeasure_volume
    haveI hP : (volume : Measure (Fin m → ℂ)).IsAddHaarMeasure := by
      first
        | infer_instance
        | exact MeasureTheory.Measure.pi.isAddHaarMeasure _
    haveI hV : (volume : Measure ((Fin m → ℂ) × ℝ)).IsAddHaarMeasure := by
      first
        | infer_instance
        | exact MeasureTheory.Measure.prod.instIsAddHaarMeasure _ _
        | (show ((volume : Measure (Fin m → ℂ)).prod (volume : Measure ℝ)).IsAddHaarMeasure
           infer_instance)
    apply finite_integral_one_add_norm
    simp only [Module.finrank_prod, Module.finrank_pi_fintype, Complex.finrank_real_complex,
      Module.finrank_self, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    push_cast
    linarith
  refine lt_of_le_of_lt (lintegral_mono (g := fun x : (Fin m → ℂ) × ℝ =>
    ENNReal.ofReal ((2 : ℝ) ^ (d / 2)) * ENNReal.ofReal ((1 + ‖x‖) ^ (-d))) fun x => ?_) ?_
  · dsimp only
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (heis_pointwise m hd0 x)
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
