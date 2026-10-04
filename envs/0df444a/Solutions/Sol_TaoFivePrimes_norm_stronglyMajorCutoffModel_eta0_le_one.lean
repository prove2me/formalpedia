-- Prove2me | solution 1 for TaoFivePrimes.norm_stronglyMajorCutoffModel_eta0_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:07:35.488624+00:00
-- url     : https://prove2.me/submissions/af037e4e-e2b1-4e35-9f73-a7e9cdb054b9

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount
import Definitions.Def_TaoFivePrimes_stronglyMajorCutoffModel
import Theorems.Thm_TaoFivePrimes_eta0_L1_eq_one

open MeasureTheory Real
open TaoFivePrimes

namespace TaoEta0

theorem eta0_nonneg (t : ℝ) : 0 ≤ eta0 t := by
  unfold eta0; split
  · positivity
  · exact le_rfl

/-- The Fourier transform of a probability cutoff is bounded by its mass, so
`‖η̂₀‖_∞ ≤ ‖η₀‖_{L¹} = 1`. -/
theorem norm_cutoffModel_eta0_le_one (scale : ℝ) (alpha : AddCircle (1 : ℝ)) :
    ‖stronglyMajorCutoffModel eta0 scale alpha‖ ≤ 1 := by
  unfold stronglyMajorCutoffModel
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hpt : ∀ t : ℝ,
      ‖(eta0 t : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I *
          ((scale * AddCircle.liftIoc (1 : ℝ) (-(1 / 2 : ℝ)) id alpha) * t))‖ = eta0 t := by
    intro t
    rw [norm_mul, Complex.norm_exp]
    simp [Complex.norm_real, Real.norm_of_nonneg (eta0_nonneg t)]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt), TaoFivePrimes.eta0_L1_eq_one]

end TaoEta0

theorem solution (scale : ℝ) (alpha : AddCircle (1 : ℝ)) :
    ‖TaoFivePrimes.stronglyMajorCutoffModel TaoFivePrimes.eta0 scale alpha‖ ≤ 1 :=
  TaoEta0.norm_cutoffModel_eta0_le_one scale alpha
