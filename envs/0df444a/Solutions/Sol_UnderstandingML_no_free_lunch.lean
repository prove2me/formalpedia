-- Prove2me | solution 1 for UnderstandingML.no_free_lunch
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T13:37:43.294902+00:00
-- url     : https://prove2.me/submissions/1ad4ec8a-4897-4080-8440-69ba584805db

import Definitions.Def_UnderstandingML_Framework
import Theorems.Thm_UnderstandingML_no_free_lunch_expectation
import Theorems.Thm_UnderstandingML_reverse_markov
import Mathlib.SetTheory.Cardinal.Finite

open MeasureTheory

namespace UnderstandingML.NFLAux

/-- The `0–1` risk of any hypothesis under a probability distribution lies in `[0, 1]`
(no measurability of the hypothesis is needed). -/
theorem risk_loss01_mem_Icc {X : Type*} [MeasurableSpace X] (D : Measure (X × Bool))
    [IsProbabilityMeasure D] (h : X → Bool) : risk loss01 D h ∈ Set.Icc (0 : ℝ) 1 := by
  have hb : ∀ z, 0 ≤ loss01 h z ∧ loss01 h z ≤ 1 := by
    intro z; unfold loss01; split_ifs <;> norm_num
  refine ⟨integral_nonneg (fun z => (hb z).1), ?_⟩
  have := norm_integral_le_of_norm_le_const (μ := D) (f := loss01 h) (C := 1)
    (Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [(hb z).1], (hb z).2⟩))
  simp only [probReal_univ, mul_one] at this
  exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ this)

end UnderstandingML.NFLAux

open UnderstandingML UnderstandingML.NFLAux

theorem solution {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (A : Learner (X × Bool) (X → Bool)) (m : ℕ) (hm : (2 * m : ℕ∞) < ENat.card X) :
    ∃ D : Measure (X × Bool), IsProbabilityMeasure D ∧
      (∃ f : X → Bool, Measurable f ∧ risk loss01 D f = 0) ∧
      ∃ E : Set (Fin m → X × Bool), MeasurableSet E ∧
        E ⊆ {S | 1 / 8 ≤ risk loss01 D (A m S)} ∧ ENNReal.ofReal (1 / 7) ≤ iidLaw D m E := by
  obtain ⟨D, hD, hf, hexp⟩ := no_free_lunch_expectation A m hm
  refine ⟨D, hD, hf, ?_⟩
  set μ := iidLaw D m with hμ
  haveI : IsProbabilityMeasure μ := by rw [hμ, iidLaw]; infer_instance
  set θ : (Fin m → X × Bool) → ℝ := fun S => risk loss01 D (A m S) with hθ
  have hθI : ∀ S, θ S ∈ Set.Icc (0 : ℝ) 1 := fun S => risk_loss01_mem_Icc D (A m S)
  -- a positive expectation forces `θ` to be a.e. strongly measurable
  have hae : AEStronglyMeasurable θ μ := by
    by_contra hns
    have : ∫ S, θ S ∂μ = 0 := integral_undef (fun hi => hns hi.aestronglyMeasurable)
    rw [this] at hexp
    norm_num at hexp
  set θ' := hae.mk θ with hθ'
  have hθ'meas : Measurable θ' := hae.stronglyMeasurable_mk.measurable
  have heq : θ =ᵐ[μ] θ' := hae.ae_eq_mk
  have hrange : ∀ᵐ S ∂μ, θ' S ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [heq] with S hS
    rw [← hS]; exact hθI S
  have hint : ∫ S, θ' S ∂μ = ∫ S, θ S ∂μ := integral_congr_ae heq.symm
  obtain ⟨-, h2, -⟩ := reverse_markov μ θ' hθ'meas hrange (a := 1 / 8) (by norm_num) (by norm_num)
  rw [hint] at h2
  have hprob : (1 : ℝ) / 7 ≤ (μ {S | 1 / 8 < θ' S}).toReal := by
    refine le_trans ?_ h2
    rw [le_div_iff₀ (by norm_num)]
    linarith
  -- remove a measurable null set containing the disagreement set of `θ` and `θ'`
  set N := toMeasurable μ {S | θ S ≠ θ' S} with hN
  have hN0 : μ N = 0 := by
    rw [hN, measure_toMeasurable]
    exact heq
  refine ⟨{S | 1 / 8 < θ' S} \ N,
    (measurableSet_lt measurable_const hθ'meas).diff (measurableSet_toMeasurable _ _), ?_, ?_⟩
  · rintro S ⟨hS1, hS2⟩
    have : θ S = θ' S := by
      by_contra hne
      exact hS2 (subset_toMeasurable μ _ hne)
    show 1 / 8 ≤ θ S
    rw [this]; exact le_of_lt hS1
  · rw [measure_diff_null hN0]
    exact ENNReal.ofReal_le_of_le_toReal hprob
