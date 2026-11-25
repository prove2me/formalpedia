-- Prove2me | solution 1 for PI.PrimeLogOverPWork.div_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:04:28.050873+00:00
-- url     : https://prove2.me/submissions/e85cc37e-7514-4ea7-a267-bf2217a27ffe

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PrimeLogOverPWork
open Finset ArithmeticFunction Nat
namespace PI.PrimeLogOverPWork
theorem _root_.solution (n d : ℕ) : (n : ℝ) / d - 1 ≤ ((n / d : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    rw [sub_le_iff_le_add, div_le_iff₀ hd']
    have h1 : (n : ℝ) = d * ((n / d : ℕ) : ℝ) + ((n % d : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod n d).symm
    have h3 : ((n % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt n hd).le
    nlinarith
end PI.PrimeLogOverPWork
