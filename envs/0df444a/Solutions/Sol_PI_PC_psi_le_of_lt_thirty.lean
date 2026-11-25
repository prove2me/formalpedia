-- Prove2me | solution 1 for PI.PC.psi_le_of_lt_thirty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:10:00.938258+00:00
-- url     : https://prove2.me/submissions/09818374-bdfd-4edb-b6f7-ca7cceee7b2f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PsiUpperBoundOfLtThirtyMulSixPow
import Theorems.Thm_PI_PC_lcmUpto_le_three_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PC
open Real
namespace PI.PC
theorem _root_.solution {x : ℝ} (h0 : 0 ≤ x) (hx : x < 30) : Chebyshev.psi x ≤ 1.1056 * x := by
  have hn : ⌊x⌋₊ < 30 := (Nat.floor_lt h0).2 (by exact_mod_cast hx)
  rw [Chebyshev.psi_eq_psi_coe_floor, Chebyshev.psi_eq_log_lcmUpto]
  have h1 : ((Nat.lcmUpto ⌊x⌋₊ : ℕ) : ℝ) ≤ (3 : ℝ) ^ ⌊x⌋₊ := by
    exact_mod_cast lcmUpto_le_three_pow _ hn
  have h2 : log ((Nat.lcmUpto ⌊x⌋₊ : ℕ) : ℝ) ≤ log ((3 : ℝ) ^ ⌊x⌋₊) :=
    log_le_log (by exact_mod_cast Nat.lcmUpto_pos _) h1
  rw [log_pow] at h2
  have h3 := log_three_lt_d9
  have h4 : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le h0
  have h5 : (0 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  have h6 : ((⌊x⌋₊ : ℕ) : ℝ) * log 3 ≤ ((⌊x⌋₊ : ℕ) : ℝ) * 1.1056 :=
    mul_le_mul_of_nonneg_left (by norm_num at h3 ⊢; linarith) h5
  nlinarith
end PI.PC
