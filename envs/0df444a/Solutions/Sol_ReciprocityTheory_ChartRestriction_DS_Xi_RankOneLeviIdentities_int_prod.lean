-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.int_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:18:53.386821+00:00
-- url     : https://prove2.me/submissions/2fc4c8e1-4731-4ac2-a1f3-e0a1a9be9cb9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ScaleInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergDualBaseVectorFormulaAlt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergMapContinuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
theorem _root_.solution (k r' : ℕ) {A p q K₁ K₂ e₁ e₂ : ℝ} (hK₁0 : 0 ≤ K₁) (hK₂0 : 0 ≤ K₂)
    (hK₁ : ∀ a b : ℝ, 0 < a → 0 < b → ∫⁻ y : Fin (2 * r' + k + 1) → ℂ, ENNReal.ofReal ((a + b * ‖y‖) ^ (-p)) ≤
      ENNReal.ofReal (K₁ * a ^ (-p) * (a / b) ^ e₁))
    (hK₂ : ∀ a b : ℝ, 0 < a → 0 < b → ∫⁻ s : ℝ, ENNReal.ofReal ((a + b * ‖s‖) ^ (-q)) ≤
      ENNReal.ofReal (K₂ * a ^ (-q) * (a / b) ^ e₂))
    (F : HPar k r' → ℝ≥0∞) {a b₁ b₂ : ℝ} (ha : 0 < a) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hF : ∀ x : HPar k r', F x ≤
      ENNReal.ofReal (2 ^ A * ((a + b₁ * ‖x.1‖) ^ (-p) * (a + b₂ * ‖x.2‖) ^ (-q)))) :
    ∫⁻ x, F x ≤ ENNReal.ofReal (2 ^ A * (K₁ * a ^ (-p) * (a / b₁) ^ e₁) * (K₂ * a ^ (-q) * (a / b₂) ^ e₂)) := by
  have hf₁ : Measurable fun y : Fin (2 * r' + k + 1) → ℂ => ENNReal.ofReal ((a + b₁ * ‖y‖) ^ (-p)) :=
    ((measurable_const.add (measurable_const.mul measurable_norm)).pow_const _).ennreal_ofReal
  have hf₂ : Measurable fun s : ℝ => ENNReal.ofReal ((a + b₂ * ‖s‖) ^ (-q)) :=
    ((measurable_const.add (measurable_const.mul measurable_norm)).pow_const _).ennreal_ofReal
  have hX : 0 ≤ K₁ * a ^ (-p) * (a / b₁) ^ e₁ :=
    mul_nonneg (mul_nonneg hK₁0 (Real.rpow_nonneg ha.le _)) (Real.rpow_nonneg (div_pos ha hb₁).le _)
  have h2A : (0 : ℝ) ≤ 2 ^ A := by positivity
  calc ∫⁻ x, F x ≤ ∫⁻ x : HPar k r', ENNReal.ofReal (2 ^ A) *
        (ENNReal.ofReal ((a + b₁ * ‖x.1‖) ^ (-p)) * ENNReal.ofReal ((a + b₂ * ‖x.2‖) ^ (-q))) := by
        refine lintegral_mono fun x => (hF x).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul h2A, ENNReal.ofReal_mul (Real.rpow_nonneg
          (add_nonneg ha.le (mul_nonneg hb₁.le (norm_nonneg _))) _)]
    _ = ENNReal.ofReal (2 ^ A) * ((∫⁻ y : Fin (2 * r' + k + 1) → ℂ, ENNReal.ofReal ((a + b₁ * ‖y‖) ^ (-p))) *
          ∫⁻ s : ℝ, ENNReal.ofReal ((a + b₂ * ‖s‖) ^ (-q))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_prod_mul (μ := (volume : Measure (Fin (2 * r' + k + 1) → ℂ)))
          (ν := (volume : Measure ℝ)) hf₁.aemeasurable hf₂.aemeasurable
    _ ≤ ENNReal.ofReal (2 ^ A) * (ENNReal.ofReal (K₁ * a ^ (-p) * (a / b₁) ^ e₁) *
          ENNReal.ofReal (K₂ * a ^ (-q) * (a / b₂) ^ e₂)) := by
        gcongr
        · exact hK₁ a b₁ ha hb₁
        · exact hK₂ a b₂ ha hb₂
    _ = _ := by
        rw [← ENNReal.ofReal_mul hX, ← ENNReal.ofReal_mul h2A]
        congr 1
        ring
end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
