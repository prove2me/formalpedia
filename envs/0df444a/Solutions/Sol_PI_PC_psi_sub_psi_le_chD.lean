-- Prove2me | solution 1 for PI.PC.psi_sub_psi_le_chD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:31:26.100812+00:00
-- url     : https://prove2.me/submissions/a9d82975-6679-4569-a93c-29f344bbf904

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_LogFactorialEqSumOfLe
import Theorems.Thm_PI_PC_chE_nonneg
import Theorems.Thm_PI_PC_chE_eq_one
import Theorems.Thm_PI_PC_chD_eq_sum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.PC
open Finset Real
open ArithmeticFunction hiding log id
open scoped Nat Chebyshev ArithmeticFunction.zeta
private theorem nat_floor_div_natCast (x : ℝ) (k : ℕ) : ⌊x / (k : ℝ)⌋₊ = ⌊x⌋₊ / k :=
  Nat.floor_div_natCast x k
private theorem chebyshev_psi_eq_sum_Ioc_vonMangoldt (x : ℝ) : ψ x = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n := by
  rfl
private theorem sum_Ioc_eq_sum_Ioc_div_six_add_sum_Ioc (N : ℕ) (f : ℕ → ℝ) :
    ∑ d ∈ Ioc 0 N, f d = ∑ d ∈ Ioc 0 (N / 6), f d + ∑ d ∈ Ioc (N / 6) N, f d := by
  rw [Finset.sum_Ioc_consecutive f (Nat.zero_le (N / 6)) (Nat.div_le_self N 6)]
end PI.PC
end
end

set_option autoImplicit false
noncomputable section
open PI PI.PC
open Finset Real
open ArithmeticFunction hiding log id
open scoped Nat Chebyshev ArithmeticFunction.zeta
namespace PI.PC
theorem _root_.solution (x : ℝ) : ψ x - ψ (x / 6) ≤ chD x := by
  have h6 : ⌊x / 6⌋₊ = ⌊x⌋₊ / 6 := by
    simpa using nat_floor_div_natCast x 6
  rw [chebyshev_psi_eq_sum_Ioc_vonMangoldt, chebyshev_psi_eq_sum_Ioc_vonMangoldt, h6, chD_eq_sum,
    sum_Ioc_eq_sum_Ioc_div_six_add_sum_Ioc ⌊x⌋₊ (fun d => Λ d),
    sum_Ioc_eq_sum_Ioc_div_six_add_sum_Ioc ⌊x⌋₊ (fun d => Λ d * chE (⌊x⌋₊ / d))]
  have hA : 0 ≤ ∑ d ∈ Ioc 0 (⌊x⌋₊ / 6), Λ d * chE (⌊x⌋₊ / d) :=
    Finset.sum_nonneg fun d _ =>
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (chE_nonneg _)
  have hB : ∑ d ∈ Ioc (⌊x⌋₊ / 6) ⌊x⌋₊, Λ d ≤
      ∑ d ∈ Ioc (⌊x⌋₊ / 6) ⌊x⌋₊, Λ d * chE (⌊x⌋₊ / d) := by
    apply Finset.sum_le_sum
    intro d hd
    rw [Finset.mem_Ioc] at hd
    have hd0 : 0 < d := by omega
    have hq1 : 1 ≤ ⌊x⌋₊ / d := Nat.div_pos hd.2 hd0
    have hq6 : ⌊x⌋₊ / d < 6 := by
      exact Nat.div_lt_of_lt_mul (by omega)
    rw [chE_eq_one hq1 hq6, mul_one]
  linarith
end PI.PC
