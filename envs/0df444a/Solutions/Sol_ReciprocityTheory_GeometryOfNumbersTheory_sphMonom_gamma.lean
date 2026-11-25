-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_gamma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:02:00.488872+00:00
-- url     : https://prove2.me/submissions/a84aa805-cb5c-4d12-b62c-54c4d6145eba

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_GaussSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomStA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Metric Set
variable {N : ℕ}
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (D n k : ℕ) (h : k = n + n) :
    Real.Gamma ((((2 * (D + 1) - 1 + k : ℕ) : ℝ) + 1) / 2) = ((D + n).factorial : ℝ) := by
  subst h
  rw [show 2 * (D + 1) - 1 + (n + n) = 2 * (D + n) + 1 by omega,
    show ((((2 * (D + n) + 1 : ℕ) : ℝ) + 1) / 2) = ((D + n : ℕ) : ℝ) + 1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial]
end ReciprocityTheory.GeometryOfNumbersTheory
