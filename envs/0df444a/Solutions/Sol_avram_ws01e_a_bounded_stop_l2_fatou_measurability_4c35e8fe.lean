-- Prove2me | solution 1 for avram_ws01e_a_bounded_stop_l2_fatou_measurability_4c35e8fe
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:29:41.827985+00:00
-- url     : https://prove2.me/submissions/3ba00c3d-48f2-4673-b511-968175a5282b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T H : ℝ≥0) (τ : Ω → ℝ≥0)
    (τn : ℕ → Ω → ℝ≥0) (grid : ℕ → Finset ℝ≥0)
    (hgrid : ∀ n ω, τn n ω ∈ grid n)
    (hT : ∀ (n : ℕ) (s : ℝ≥0), s ∈ grid n → s ≤ T)
    (hstop : ∀ (n : ℕ) (s : ℝ≥0), s ∈ grid n →
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s})
    (hbound : ∀ n ω, τn n ω ≤ H)
    (hlim : ∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω)))
    (habove : ∀ ω n, τ ω ≤ τn n ω) 
    : (let f : ℕ → Ω → ℝ≥0∞ := (fun n ω => ENNReal.ofReal ((Real.exp (θ * X.X (τn n ω) ω - (τn n ω : ℝ) * X.ψ θ)) ^ 2)); ∀ n, Measurable (f n)) := by
  intro f n
  have hm : ∀ s : ℝ≥0, Measurable (fun ω => ENNReal.ofReal
      ((Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ)) ^ 2)) := by
    intro s
    have hXs : Measurable (X.X s) := (X.adapted s).mono (𝓕.le s) le_rfl
    fun_prop
  have key : f n = fun ω => ∑ s ∈ grid n, {ω' | τn n ω' = s}.indicator
      (fun ω => ENNReal.ofReal ((Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ)) ^ 2)) ω := by
    funext ω
    rw [Finset.sum_eq_single (τn n ω)]
    · rw [Set.indicator_of_mem (show ω ∈ {ω' | τn n ω' = τn n ω} from rfl)]
    · intro b _ hb
      rw [Set.indicator_of_notMem]
      exact fun h => hb h.symm
    · intro h
      exact absurd (hgrid n ω) h
  rw [key]
  exact Finset.measurable_sum _ (fun s hs => (hm s).indicator (𝓕.le s _ (hstop n s hs)))
