-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.bounded_size_bias_strict_gap
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:45:26.864165+00:00
-- url     : https://prove2.me/submissions/e7d4fdc2-3bd1-449d-8fd5-f6016366cc15

import Theorems.Thm_ZeroFreeRRG_Hardcore_nontrivial_size_bias_strict_coupling
import Theorems.Thm_ZeroFreeRRG_Hardcore_bounded_hardcore_expected_gap
import Mathlib
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (d : ℕ) (hd : 2 ≤ d) (θ C : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hbound : ∀ᵐ x ∂μ, 0 ≤ x ∧ x ≤ C)
    (hint : Integrable (fun x : ℝ => x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1) (hne : μ ≠ Measure.dirac 1) :
    ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧
      Measure.map Prod.fst π = μ ∧
      Measure.map Prod.snd π = μ.withDensity (fun x => ENNReal.ofReal x) ∧
      let g := fun (xs : Fin d → ℝ × ℝ) (S : Finset (Fin d)) =>
        Real.log (1+θ*∏ a, if a ∈ S then (xs a).2 else (xs a).1)
      0 < ∫ xs, g xs Finset.univ - g xs ∅ - ∑ i, (g xs {i}-g xs ∅)
        ∂(Measure.pi fun _ : Fin d => π) := by
  have hpos : ∀ᵐ x ∂μ, 0 ≤ x := hbound.mono (fun _ hx => hx.1)
  obtain ⟨π,hprob,hfst,hsnd,horder,hs,hprod⟩ :=
    nontrivial_size_bias_strict_coupling μ hpos hint hmean hne
  letI : IsProbabilityMeasure π := hprob
  have hf : ∀ᵐ p ∂π, 0 ≤ p.1 := by
    apply (ae_map_iff measurable_fst.aemeasurable (measurableSet_le measurable_const measurable_id)).1
    simpa [hfst] using hpos
  have hsize : ∀ᵐ x ∂(μ.withDensity (fun x => ENNReal.ofReal x)), x ≤ C :=
    (withDensity_absolutelyContinuous μ _).ae_le (hbound.mono (fun _ hx => hx.2))
  have hsbound : ∀ᵐ p ∂π, p.2 ≤ C := by
    apply (ae_map_iff measurable_snd.aemeasurable (measurableSet_le measurable_id measurable_const)).1
    simpa [hsnd] using hsize
  have hπbound : ∀ᵐ p ∂π, 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ C := by
    filter_upwards [hf,horder,hsbound] with p ha hb hc
    exact ⟨ha,hb,hc⟩
  have hp : 0 < π {p | 0 < p.1} := by
    have hz : 0 < μ {x | 0 < x} := by
      by_contra hn
      have hz : μ {x | 0 < x} = 0 := le_antisymm (not_lt.mp hn) bot_le
      have hno : ∀ᵐ x ∂μ, ¬0 < x := ae_iff.mpr (by simpa only [not_not] using hz)
      have heq : ∀ᵐ x ∂μ, x = 0 := by
        filter_upwards [hpos,hno] with x hx hn'
        exact le_antisymm (le_of_not_gt hn') hx
      have hh : (∫ x, x ∂μ) = 0 := by
        calc
          _ = ∫ _x, (0:ℝ) ∂μ := integral_congr_ae heq
          _ = 0 := integral_zero _ _
      linarith
    change 0 < μ (Ioi (0:ℝ)) at hz
    rw [← hfst, Measure.map_apply measurable_fst measurableSet_Ioi] at hz
    exact hz
  refine ⟨π,hprob,hfst,hsnd,?_⟩
  exact bounded_hardcore_expected_gap d hd θ C hθ hC π hπbound hs hp
