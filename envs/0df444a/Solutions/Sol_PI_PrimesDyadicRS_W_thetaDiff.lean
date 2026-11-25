-- Prove2me | solution 1 for PI.PrimesDyadicRS.W.thetaDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:05:41.337528+00:00
-- url     : https://prove2.me/submissions/f46dcae0-3920-44c8-9c02-a18b209a4bcf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PrimesDyadicRS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_ThetaDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_FloorHalf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_ClaimOfTwo

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
theorem _root_.solution : ThetaDiff := by
  intro y hy
  have hab : ⌊y⌋₊ ≤ ⌊2 * y⌋₊ := Nat.floor_mono (by linarith)
  have hsub : Nat.primesLE ⌊y⌋₊ ⊆ Nat.primesLE ⌊2 * y⌋₊ := Nat.primesLE_mono hab
  rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE,
    ← Finset.sum_sdiff hsub, add_sub_cancel_right]
  have hcard : ((Nat.primesLE ⌊2 * y⌋₊ \ Nat.primesLE ⌊y⌋₊).card : ℝ) =
      (Nat.primeCounting ⌊2 * y⌋₊ : ℝ) - (Nat.primeCounting ⌊y⌋₊ : ℝ) := by
    rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub),
      Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
  rw [← hcard, ← nsmul_eq_mul]
  apply Finset.sum_le_card_nsmul
  intro p hp
  have hp' := (Finset.mem_sdiff.1 hp).1
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast Nat.two_le_of_mem_primesLE hp'
  have hle : (p : ℝ) ≤ 2 * y :=
    (Nat.cast_le.2 (Nat.le_of_mem_primesLE hp')).trans (Nat.floor_le (by linarith))
  exact Real.log_le_log (by linarith) hle
end PI.PrimesDyadicRS.W
