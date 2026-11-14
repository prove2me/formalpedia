-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.size_bias_ordered_coupling_strict
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:24:20.394844+00:00
-- url     : https://prove2.me/submissions/534d8500-1afd-493b-b74c-9cc852a451c6

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (π : Measure (ℝ × ℝ))
    (hpos : ∀ᵐ x ∂μ, 0 ≤ x) (hne : μ ≠ Measure.dirac 1)
    (hfst : Measure.map Prod.fst π = μ)
    (hsnd : Measure.map Prod.snd π = μ.withDensity (fun x => ENNReal.ofReal x))
    (horder : ∀ᵐ p ∂π, p.1 ≤ p.2) : 0 < π {p | p.1 < p.2} := by
  by_contra hn
  have hz : π {p | p.1 < p.2} = 0 := le_antisymm (not_lt.mp hn) bot_le
  have hno : ∀ᵐ p ∂π, ¬p.1 < p.2 := ae_iff.mpr (by simpa only [not_not] using hz)
  have heq : ∀ᵐ p ∂π, p.1 = p.2 := by
    filter_upwards [horder,hno] with p hp hn'
    exact le_antisymm hp (le_of_not_gt hn')
  have hmaps : Measure.map Prod.fst π = Measure.map Prod.snd π := Measure.map_congr heq
  have hμ : μ.withDensity (fun x => ENNReal.ofReal x) = μ.withDensity 1 := by
    calc
      _ = Measure.map Prod.snd π := hsnd.symm
      _ = Measure.map Prod.fst π := hmaps.symm
      _ = μ := hfst
      _ = μ.withDensity 1 := withDensity_one.symm
  have hden : (fun x : ℝ => ENNReal.ofReal x) =ᵐ[μ] (1 : ℝ → ℝ≥0∞) :=
    (withDensity_eq_iff_of_sigmaFinite measurable_id.ennreal_ofReal.aemeasurable measurable_const.aemeasurable).1 hμ
  have hone : ∀ᵐ x ∂μ, x = 1 := by
    filter_upwards [hden,hpos] with x hx hx0
    have hh := congrArg ENNReal.toReal hx
    simpa [ENNReal.toReal_ofReal hx0] using hh
  apply hne
  calc
    μ = Measure.map id μ := Measure.map_id.symm
    _ = Measure.map (fun _ => (1:ℝ)) μ := Measure.map_congr hone
    _ = Measure.dirac 1 := by simp
