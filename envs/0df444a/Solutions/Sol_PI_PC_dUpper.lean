-- Prove2me | solution 1 for PI.PC.dUpper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:26:30.426198+00:00
-- url     : https://prove2.me/submissions/04459536-7643-4a2f-9d65-45631438e776

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_LogFactorialLe
import Theorems.Thm_PI_PC_log_thirty_ge
import Theorems.Thm_PI_PC_lfUpper
import Theorems.Thm_PI_PC_lfLower
import Theorems.Thm_PI_PC_main_term
import Theorems.Thm_PI_PC_stir_log_thirty

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
theorem _root_.solution : DUpper := by
  intro x hx
  simp only [chD]
  have hx0 : (0 : ℝ) < x := by linarith
  have l1 := lfUpper x (by linarith)
  have l30 := lfUpper (x / 30) (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have u2 := lfLower (x / 2) (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have u3 := lfLower (x / 3) (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have u5 := lfLower (x / 5) (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have hm := main_term hx0
  have h2 : log (x / 2) = log x - log 2 := Real.log_div hx0.ne' (by norm_num)
  have h3 : log (x / 3) = log x - log 3 := Real.log_div hx0.ne' (by norm_num)
  have h5 : log (x / 5) = log x - log 5 := Real.log_div hx0.ne' (by norm_num)
  have h30 : log (x / 30) = log x - log 30 := Real.log_div hx0.ne' (by norm_num)
  have hl30 := log_thirty_ge
  have hs := stir_log_thirty
  linarith
end PI.PC
