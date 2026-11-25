-- Prove2me | solution 1 for PI.PC.lfLower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:20:11.001802+00:00
-- url     : https://prove2.me/submissions/f80868d1-58ba-41fe-94aa-077d6609347e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_LogFactorialLe
import Theorems.Thm_PI_PC_h_le
import Theorems.Thm_PI_PC_log_two_pi_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.PC
open Finset Real
open scoped Nat
namespace PI.PC
theorem _root_.solution : LfLower := by
  intro y hy
  simp only [lf]
  have hn1 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by simpa using hy)
  have hn1' : (1 : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hn1
  have hy' : y ≤ (⌊y⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one y).le
  have hS := Stirling.le_log_factorial_stirling (n := ⌊y⌋₊ + 1) (Nat.succ_ne_zero _)
  have hfac : Real.log (((⌊y⌋₊ + 1) ! : ℕ) : ℝ) =
      Real.log ((⌊y⌋₊ : ℝ) + 1) + Real.log ((⌊y⌋₊ ! : ℕ) : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    push_cast
    ring
  have h2π := log_two_pi_ge
  have hh := h_le hy hy' (by linarith)
  push_cast at hS hfac
  linarith
end PI.PC
