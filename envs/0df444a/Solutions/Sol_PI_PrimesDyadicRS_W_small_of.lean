-- Prove2me | solution 1 for PI.PrimesDyadicRS.W.small_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:11:15.635565+00:00
-- url     : https://prove2.me/submissions/b5e74fa2-04d0-4535-9215-68c1f660d198

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PrimesDyadicRS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_ThetaDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PsiLowerBoundHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_FloorHalf
import Theorems.Thm_PI_PrimesDyadicRS_W_floor_half

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
theorem _root_.solution (hS : SmallNat) : ∀ y : ℝ, 41 / 2 ≤ y → y < 65536 → At y := by
  intro y h1 h2
  have hy0 : 0 ≤ 2 * y := by linarith
  have h41 : 41 ≤ ⌊2 * y⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hlt : ⌊2 * y⌋₊ < 131072 := (Nat.floor_lt hy0).2 (by push_cast; linarith)
  have key := hS _ h41 hlt
  have hhy : (⌊2 * y⌋₊ : ℝ) ≤ 2 * y := Nat.floor_le hy0
  have hyh : 2 * y < ⌊2 * y⌋₊ + 1 := Nat.lt_floor_add_one _
  have h41r : (41 : ℝ) ≤ ⌊2 * y⌋₊ := by exact_mod_cast h41
  have hh2 : (0 : ℝ) < (⌊2 * y⌋₊ : ℝ) / 2 := by linarith
  have hlog0 : 0 < Real.log ((⌊2 * y⌋₊ : ℝ) / 2) := Real.log_pos (by linarith)
  have hlog : Real.log ((⌊2 * y⌋₊ : ℝ) / 2) ≤ Real.log y := Real.log_le_log hh2 (by linarith)
  have hlogy : 0 < Real.log y := lt_of_lt_of_le hlog0 hlog
  unfold At
  rw [floor_half y]
  set D := (Nat.primeCounting ⌊2 * y⌋₊ : ℝ) - (Nat.primeCounting (⌊2 * y⌋₊ / 2) : ℝ) with hDdef
  have hD : 0 < D := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_le_mul_of_nonneg_right hc hlog0.le]
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hlog hD.le]
end PI.PrimesDyadicRS.W
