-- Prove2me | solution 1 for Rudin.ch10_iterated_integral_ordered
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T04:40:09.549686+00:00
-- url     : https://prove2.me/submissions/0613f6b8-d7c4-4788-8cbc-c1d0ae9953de

import Mathlib

open Filter Topology MeasureTheory

/-- Rudin, Theorem 10.2 with the ordering hypotheses of Definition 10.1: for a function
continuous on the 2-cell `[a,b] × [c,d]` the two iterated integrals agree. -/
theorem solution (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) (f : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d)) :
    (∫ x in a..b, ∫ y in c..d, f x y) = ∫ y in c..d, ∫ x in a..b, f x y := by
  have hK : IsCompact (Set.Icc a b ×ˢ Set.Icc c d) := isCompact_Icc.prod isCompact_Icc
  have hint : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d) volume :=
    hf.integrableOn_compact hK
  have hsub : Set.Ioc a b ×ˢ Set.Ioc c d ⊆ Set.Icc a b ×ˢ Set.Icc c d :=
    Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self
  have hI : Integrable (Function.uncurry f)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc c d))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hint.mono_set hsub
  simp_rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  exact integral_integral_swap hI
