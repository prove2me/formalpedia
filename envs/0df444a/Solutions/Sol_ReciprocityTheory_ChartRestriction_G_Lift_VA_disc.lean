-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Lift.VA.disc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:32:49.149827+00:00
-- url     : https://prove2.me/submissions/093fb5d8-ef54-4c31-a40d-c71087567c98

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_LiftSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_ValuationApproximation_LargeSmall
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_ValuationApproximation_RhoProjectionAssembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Lift ReciprocityTheory.ChartRestriction.G.Lift.VA
open WithZero
namespace ReciprocityTheory.ChartRestriction.G.Lift.VA
theorem _root_.solution (M ε : WithZero (Multiplicative ℤ)) (hε : ε ≠ 0) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ m', m ≤ m' → ∀ g h : WithZero (Multiplicative ℤ),
      g < 1 → h ≤ M → g ^ m' * h < ε := by
  obtain ⟨e, rfl⟩ : ∃ e : ℤ, ε = exp e := ⟨log ε, (exp_log hε).symm⟩
  obtain ⟨a, ha⟩ : ∃ a : ℤ, M ≤ exp a := by
    rcases eq_or_ne M 0 with rfl | hM
    · exact ⟨0, zero_le⟩
    · exact ⟨log M, (exp_log hM).ge⟩
  refine ⟨(a - e + 1).toNat + 1, by omega, fun m' hm' g h hg hh => ?_⟩
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [zero_pow (by omega), zero_mul]
    exact exp_pos
  · have hg1 : g ≤ exp (-1) := by
      rw [← exp_log hg0] at hg ⊢
      rw [← exp_zero, exp_lt_exp] at hg
      rw [exp_le_exp]
      omega
    calc g ^ m' * h ≤ exp (-1) ^ m' * exp a :=
          mul_le_mul' (pow_le_pow_left' hg1 m') (hh.trans ha)
      _ = exp (-(m' : ℤ) + a) := by
          rw [← exp_nsmul, ← exp_add]
          congr 1
          rw [smul_neg, nsmul_eq_mul, mul_one]
      _ < exp e := by
          rw [exp_lt_exp]
          omega
end ReciprocityTheory.ChartRestriction.G.Lift.VA
