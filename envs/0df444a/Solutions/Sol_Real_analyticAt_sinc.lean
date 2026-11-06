-- Prove2me | solution 1 for Real.analyticAt_sinc
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:19:59.067946+00:00
-- url     : https://prove2.me/submissions/19e393ce-eb0a-4633-ba93-632a91fa608e

import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

theorem solution (x : ℝ) : AnalyticAt ℝ Real.sinc x := by
  by_cases hx : x = 0
  · subst x
    rw [Real.sinc_eq_dslope]
    obtain ⟨p, hp⟩ := Real.analyticAt_sin (x := (0 : ℝ))
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  · have h : Filter.EventuallyEq (nhds x) Real.sinc (fun y => Real.sin y / y) :=
      Filter.Eventually.mono
        (show ∀ᶠ y in nhds x, y ≠ 0 from isOpen_ne.mem_nhds hx)
        (fun y hy => Real.sinc_of_ne_zero hy)
    exact (analyticAt_congr h).2 (Real.analyticAt_sin.div analyticAt_id hx)
