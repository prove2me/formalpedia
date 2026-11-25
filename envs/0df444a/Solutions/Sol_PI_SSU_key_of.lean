-- Prove2me | solution 1 for PI.SSU.key_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:22:49.35247+00:00
-- url     : https://prove2.me/submissions/e19e2ca1-9026-46fc-a175-d27c9f5f7008

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesUniqueness_Complete
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesUniqueness_CoefShift
import Theorems.Thm_PI_SSU_coef_shift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SSU
open Complex
namespace PI.SSU
theorem _root_.solution (hS : ShiftInv) (hC : Complete) : KeyP := by
  intro f τ K k hf hK hk h1 hτ h0
  apply hC f hf h1
  have hrel : ∀ n : ℤ, coef f n = 0 ↔ coef f (n + k) = 0 := by
    intro n
    rw [coef_shift hS f τ K k hf h1 hτ n, mul_eq_zero,
      or_iff_right (mul_ne_zero hK (Complex.exp_ne_zero _))]
  have H : ∀ n : ℤ, coef f n = 0 ↔ coef f (n + 1) = 0 := by
    intro n
    rcases hk with rfl | rfl
    · exact hrel n
    · have := hrel (n + 1)
      rw [show n + 1 + -1 = n by ring] at this
      exact this.symm
  intro n
  induction n using Int.induction_on with
  | zero => exact h0
  | succ i hi => exact (H i).mp hi
  | pred i hi =>
    have := H (-(i:ℤ) - 1)
    rw [show -(i:ℤ) - 1 + 1 = -i by ring] at this
    exact this.mpr hi
end PI.SSU
