-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.TayInvPow.cf_rec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:54:26.658548+00:00
-- url     : https://prove2.me/submissions/ebe6d3bd-8458-4d1c-ae31-3dc34193dba6

import Definitions.Def_Formalism_PeriodIntegrals_TayInvPow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TaylorInversePower_SumMultinomialSub
import Theorems.Thm_PI_UnitaryGroupMassFormula_TayInvPow_deg_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_TayInvPow_deg_single
import Theorems.Thm_PI_UnitaryGroupMassFormula_TayInvPow_deg_eq_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_TayInvPow_cprod_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_TayInvPow_cprod_single
import Theorems.Thm_PI_UnitaryGroupMassFormula_TayInvPow_sum_multinomial_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.TayInvPow
open MvPowerSeries
variable {σ : Type*} {A : Type*} [CommRing A]
namespace PI.UnitaryGroupMassFormula.TayInvPow
theorem _root_.solution (c : σ →₀ A) (s t : A) (hst : s * t = 1) (k : ℕ) (β : σ →₀ ℕ) :
    s * cf c t (k + 1) β + ∑ p ∈ β.support, c p * cf c t (k + 1) (β - Finsupp.single p 1 : σ →₀ ℕ) =
      cf c t k β := by
  classical
  by_cases hβ : β = 0
  · subst hβ
    simp only [cf, deg, cprod, Finsupp.sum_zero_index, Finsupp.prod_zero_index, Finsupp.support_zero,
      Finset.sum_empty, add_zero, Nat.multinomial_empty, pow_zero, Nat.choose_zero_right, Nat.cast_one,
      one_mul, mul_one]
    linear_combination t ^ k * hst
  · obtain ⟨m, hm⟩ : ∃ m, deg β = m + 1 := ⟨deg β - 1, by have := mt deg_eq_zero.1 hβ; omega⟩
    have hterm : ∀ p ∈ β.support, c p * cf c t (k + 1) (β - Finsupp.single p 1 : σ →₀ ℕ) =
        ((-1) ^ m * (((k + m).choose m : ℕ) : A) * cprod c β * t ^ (k + m + 1)) *
          ((Nat.multinomial β.support (β - Finsupp.single p 1 : σ →₀ ℕ) : ℕ) : A) := by
      intro p hp
      have hp' : 1 ≤ β p := Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hp)
      have hdec : β - Finsupp.single p 1 + Finsupp.single p 1 = β :=
        tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hp')
      have hdeg : deg (β - Finsupp.single p 1 : σ →₀ ℕ) = m := by
        have := deg_add (β - Finsupp.single p 1 : σ →₀ ℕ) (Finsupp.single p 1)
        rw [hdec, deg_single] at this
        omega
      have hcp : cprod c β = cprod c (β - Finsupp.single p 1 : σ →₀ ℕ) * c p := by
        conv_lhs => rw [← hdec]
        rw [cprod_add, cprod_single, pow_one]
      have hM : Nat.multinomial (β - Finsupp.single p 1 : σ →₀ ℕ).support (β - Finsupp.single p 1 : σ →₀ ℕ) =
          Nat.multinomial β.support (β - Finsupp.single p 1 : σ →₀ ℕ) :=
        (Finsupp.multinomial_eq _).symm.trans
          (Finsupp.multinomial_of_support_subset Finsupp.support_tsub).symm
      unfold cf
      rw [hdeg, hM, hcp, show k + 1 + m - 1 = k + m by omega, show k + 1 + m = k + m + 1 by omega]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Nat.cast_sum, sum_multinomial_sub β hβ]
    unfold cf
    rw [hm, show k + 1 + (m + 1) - 1 = k + m + 1 by omega, show k + (m + 1) - 1 = k + m by omega,
      Nat.choose_succ_succ]
    push_cast
    linear_combination ((-1) ^ (m + 1) * ((((k + m).choose m : ℕ) : A) + (((k + m).choose (m + 1) : ℕ) : A)) *
      ((Nat.multinomial β.support β : ℕ) : A) * cprod c β * t ^ (k + m + 1)) * hst
end PI.UnitaryGroupMassFormula.TayInvPow
