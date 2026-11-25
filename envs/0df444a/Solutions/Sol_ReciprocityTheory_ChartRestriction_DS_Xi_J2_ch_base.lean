-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.ch_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:24:19.320819+00:00
-- url     : https://prove2.me/submissions/e5e4d671-f104-4b9a-a344-ae9eca52e78b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_base_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_volume_univ_fin_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Module
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.J2
theorem _root_.solution (m : ℕ) (ν : Fin 1 → ℝ) (hν : 0 < ν 0) : CHInt 0 m ν < ∞ := by
  have hv := hν
  have hf1 : MeasureTheory.Integrable
      (fun u : Fin m → ℂ => (1 + ‖u‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) := by
    apply integrable_rpow_neg_one_add_norm_sq
    simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    push_cast
    linarith
  have hf2 : MeasureTheory.Integrable (fun b : ℝ => (1 + ‖b‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2)) := by
    apply integrable_rpow_neg_one_add_norm_sq
    rw [Module.finrank_self]
    push_cast
    linarith
  have hm1 : Measurable fun u : Fin m → ℂ => ENNReal.ofReal ((1 + ‖u‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) := by
    first
    | fun_prop
    | measurability
  have hm2 : Measurable fun b : ℝ => ENNReal.ofReal ((1 + ‖b‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2)) := by
    first
    | fun_prop
    | measurability
  have hprod : ∫⁻ y : (Fin m → ℂ) × ℝ, ENNReal.ofReal ((1 + ‖y.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) *
      ENNReal.ofReal ((1 + ‖y.2‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2)) < ∞ := by
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.lintegral_prod_mul hm1.aemeasurable hm2.aemeasurable]
    exact ENNReal.mul_lt_top hf1.lintegral_lt_top hf2.lintegral_lt_top
  have hpeel : ∀ {β : Type} [MeasureSpace β] [SFinite (volume : Measure β)] (g : β → ℝ≥0∞), Measurable g →
      ∫⁻ x : (Fin 0 → ℂ) × β, g x.2 = ∫⁻ y, g y := by
    intro β _ _ g hg
    rw [MeasureTheory.Measure.volume_eq_prod,
      MeasureTheory.lintegral_prod (fun x : (Fin 0 → ℂ) × β => g x.2) (hg.comp measurable_snd).aemeasurable]
    simp only [MeasureTheory.lintegral_const, volume_univ_fin_zero, mul_one]
  have hbound : CHInt 0 m ν ≤ ∫⁻ x : Xp 0 m, ENNReal.ofReal (2 ^ ((m : ℝ) + ν 0 / 2)) *
      (ENNReal.ofReal ((1 + ‖x.2.2.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) *
        ENNReal.ofReal ((1 + ‖x.2.2.2‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2))) := by
    unfold CHInt
    refine MeasureTheory.lintegral_mono fun x => ?_
    rw [Fin.prod_univ_one,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖x.2.2.1‖ ^ 2) _),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ ((m : ℝ) + ν 0 / 2))]
    exact ENNReal.ofReal_le_ofReal (base_pt m (ν 0) hν x)
  refine lt_of_le_of_lt hbound ?_
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  have hg1 : Measurable fun z : (Fin m → ℂ) × ℝ => ENNReal.ofReal ((1 + ‖z.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) *
      ENNReal.ofReal ((1 + ‖z.2‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2)) :=
    (hm1.comp measurable_fst).mul (hm2.comp measurable_snd)
  have e1 : ∫⁻ x : Xp 0 m, ENNReal.ofReal ((1 + ‖x.2.2.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) *
      ENNReal.ofReal ((1 + ‖x.2.2.2‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2)) =
      ∫⁻ y : (Fin 0 → ℂ) × ((Fin m → ℂ) × ℝ), ENNReal.ofReal ((1 + ‖y.2.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) *
        ENNReal.ofReal ((1 + ‖y.2.2‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2)) :=
    hpeel (fun y : (Fin 0 → ℂ) × ((Fin m → ℂ) × ℝ) =>
      ENNReal.ofReal ((1 + ‖y.2.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) *
        ENNReal.ofReal ((1 + ‖y.2.2‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2))) (hg1.comp measurable_snd)
  have e2 : ∫⁻ y : (Fin 0 → ℂ) × ((Fin m → ℂ) × ℝ), ENNReal.ofReal ((1 + ‖y.2.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) *
        ENNReal.ofReal ((1 + ‖y.2.2‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2)) =
      ∫⁻ z : (Fin m → ℂ) × ℝ, ENNReal.ofReal ((1 + ‖z.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) *
        ENNReal.ofReal ((1 + ‖z.2‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2)) :=
    hpeel (fun z : (Fin m → ℂ) × ℝ => ENNReal.ofReal ((1 + ‖z.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) *
        ENNReal.ofReal ((1 + ‖z.2‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2))) hg1
  rw [e1, e2]
  exact hprod
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
