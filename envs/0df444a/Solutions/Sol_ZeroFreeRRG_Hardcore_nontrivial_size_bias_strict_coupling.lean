-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.nontrivial_size_bias_strict_coupling
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:38:25.131927+00:00
-- url     : https://prove2.me/submissions/cf6f2da2-6cc9-4db1-b524-d322ac18461b

import Theorems.Thm_ZeroFreeRRG_Hardcore_mean_one_size_bias_monotone_coupling
import Theorems.Thm_ZeroFreeRRG_Hardcore_size_bias_ordered_coupling_strict
import Theorems.Thm_ZeroFreeRRG_Hardcore_size_bias_strict_product_event
import Mathlib
set_option autoImplicit false
open MeasureTheory Set

private theorem positive_mean_event (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ x ∂μ, 0 ≤ x) (hmean : (∫ x, x ∂μ) = 1) :
    0 < μ {x | 0 < x} := by
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

open ZeroFreeRRG.Hardcore

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ x ∂μ, 0 ≤ x) (hint : Integrable (fun x => x) μ)
    (hmean : (∫ x, x ∂μ) = 1) (hne : μ ≠ Measure.dirac 1) :
    ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧
      Measure.map Prod.fst π = μ ∧
      Measure.map Prod.snd π = μ.withDensity (fun x => ENNReal.ofReal x) ∧
      (∀ᵐ p ∂π, p.1 ≤ p.2) ∧ (0 < π {p | p.1 < p.2}) ∧
      (∀ d : ℕ, ∀ hd : 2 ≤ d,
        0 < (Measure.pi fun _ : Fin d => π)
          {xs | (xs ⟨0,by omega⟩).1 < (xs ⟨0,by omega⟩).2 ∧
            (xs ⟨1,by omega⟩).1 < (xs ⟨1,by omega⟩).2 ∧
            ∀ a, a ≠ ⟨0,by omega⟩ → a ≠ ⟨1,by omega⟩ → 0 < (xs a).1}) := by
  obtain ⟨π,hprob,hfst,hsnd,horder⟩ := mean_one_size_bias_monotone_coupling μ hpos hint hmean
  letI : IsProbabilityMeasure π := hprob
  have hs := size_bias_ordered_coupling_strict μ π hpos hne hfst hsnd horder
  have hp : 0 < π {p | 0 < p.1} := by
    have hh := positive_mean_event μ hpos hmean
    change 0 < μ (Ioi (0:ℝ)) at hh
    rw [← hfst, Measure.map_apply measurable_fst measurableSet_Ioi] at hh
    exact hh
  exact ⟨π,hprob,hfst,hsnd,horder,hs,fun d hd => size_bias_strict_product_event d hd π hs hp⟩
