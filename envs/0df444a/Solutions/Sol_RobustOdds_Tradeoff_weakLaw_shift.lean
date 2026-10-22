-- Prove2me | solution 1 for RobustOdds.Tradeoff.weakLaw_shift
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:00:38.827134+00:00
-- url     : https://prove2.me/submissions/499d7634-474d-493b-8381-058aa8fad7a5

import Mathlib
import Definitions.Def_RobustOdds_Tradeoff_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory RobustOdds.Tradeoff

theorem solution (d : ℕ) (η : ℝ) :
    ∀ y : ℝ, (weakLaw d η y).map (fun z i => z i - 2 * η * y) = weakLaw d η (-y) := by
  intro y
  unfold weakLaw
  have := Measure.pi_map_pi (μ := fun _ : Fin d => gaussianReal (y * η) 1)
    (f := fun _ (t : ℝ) => t - 2 * η * y) (fun i => by fun_prop)
  rw [this]
  simp only [gaussianReal_map_sub_const]
  congr 1
  funext i
  congr 1
  ring
