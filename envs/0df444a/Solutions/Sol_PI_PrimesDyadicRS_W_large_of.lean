-- Prove2me | solution 1 for PI.PrimesDyadicRS.W.large_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:52:12.100187+00:00
-- url     : https://prove2.me/submissions/52d3c643-f924-42b0-a723-72558e5a154e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PrimesDyadicRS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_ThetaDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PsiLowerBoundHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_FloorHalf
import Theorems.Thm_PI_PC_psiLowerBound_holds
import Theorems.Thm_PI_PC_psiUpperBound_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PrimesDyadicRS PI.PrimesDyadicRS.W
namespace PI.PrimesDyadicRS.W
theorem _root_.solution (hT : ThetaDiff) (hP : PsiTheta) (hR : RealIneq) :
    ∀ y : ℝ, 65536 ≤ y → At y := by
  intro y hy
  have h1 := PI.PC.psiLowerBound_holds (2 * y) (by linarith)
  have h2 := PI.PC.psiUpperBound_holds y (by linarith)
  have h3 := hP (2 * y) (by linarith)
  have hs : (1 : ℝ) ≤ Real.sqrt (2 * y) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have h4 := PI.PC.psiUpperBound_holds (Real.sqrt (2 * y)) hs
  have h5 := Chebyshev.theta_le_psi y
  have h6 := hT y (by linarith)
  have h7 := hR y hy
  have hL : 0 < Real.log (2 * y) := Real.log_pos (by linarith)
  unfold At
  have h8 : 3 * y / (5 * Real.log y) * Real.log (2 * y) <
      ((Nat.primeCounting ⌊2 * y⌋₊ : ℝ) - (Nat.primeCounting ⌊y⌋₊ : ℝ)) * Real.log (2 * y) := by
    linarith
  exact lt_of_mul_lt_mul_right h8 hL.le
end PI.PrimesDyadicRS.W
