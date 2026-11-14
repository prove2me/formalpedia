-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.cavity_dirac_membership
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:47:42.390688+00:00
-- url     : https://prove2.me/submissions/33505076-fda7-4ca8-ae5c-8f80ced95d68

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Mathlib
set_option autoImplicit false
open MeasureTheory ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (t : ℝ) (hπ : m.pi t ∈ stdSimplex ℝ m.Spin) :
    diracPi m t ∈ cavityLaws m t := by
  classical
  constructor
  · change Measure.dirac (m.pi t) (stdSimplex ℝ m.Spin)ᶜ = 0
    rw [Measure.dirac_apply]
    simp [hπ]
  · intro a
    change (∫ μ : m.Spin → ℝ, μ a ∂Measure.dirac (m.pi t)) = m.pi t a
    rw [integral_dirac]
