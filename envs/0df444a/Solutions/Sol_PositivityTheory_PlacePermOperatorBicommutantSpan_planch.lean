-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.planch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:21:41.343733+00:00
-- url     : https://prove2.me/submissions/d27d52ed-9205-4836-9beb-90edc31d9380

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_IsOpenCoset
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_chi_cont
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_sb_int
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_fou_sb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set
open scoped ENNReal ComplexConjugate
noncomputable section
open PositivityTheory PositivityTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.CompanionTheory.SW.Core
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
variable [MeasurableSpace V] {χ : V → V → ℂ} {μ : Measure V}
variable (h : NADual V χ μ)
include h
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution {φ : V → ℂ} (hφ : SB φ) : ∫ y, ‖fou χ μ φ y‖ ^ 2 ∂μ = ∫ x, ‖φ x‖ ^ 2 ∂μ := by
  have hh := h
  obtain ⟨_, _, _, _, _, _, -⟩ := hh
  obtain ⟨hF, hinv⟩ := fou_sb h hφ
  have hc : Integrable (fun x => conj (φ x)) μ := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp (sb_int h hφ)
  have hint : Integrable (Function.uncurry fun y x => fou χ μ φ y * conj (φ x) * χ y (-x)) (μ.prod μ) :=
    ((sb_int h hF).mul_prod hc).mul_bdd (c := 1)
      ((chi_cont h).comp (continuous_fst.prodMk continuous_snd.neg)).aestronglyMeasurable
      (ae_of_all _ fun p => (chi_norm h _ _).le)
  have e := integral_integral_swap hint
  have e1 : ∀ y, ∫ x, fou χ μ φ y * conj (φ x) * χ y (-x) ∂μ = ((‖fou χ μ φ y‖ ^ 2 : ℝ) : ℂ) := fun y => by
    simp only [mul_assoc, integral_const_mul]
    rw [Complex.ofReal_pow, ← Complex.mul_conj', fou, ← integral_conj]
    congr 2
    funext x
    rw [map_mul, chi_sym h y, chi_neg h]
  have e2 : ∀ x, ∫ y, fou χ μ φ y * conj (φ x) * χ y (-x) ∂μ = ((‖φ x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    have := hinv (-x)
    rw [neg_neg, fou] at this
    simp only [mul_right_comm _ (conj (φ x)), integral_mul_const]
    rw [this, Complex.ofReal_pow, Complex.mul_conj']
  simp only [e1, e2, integral_ofReal] at e
  exact_mod_cast e
end PositivityTheory.PlacePermOperatorBicommutantSpan
