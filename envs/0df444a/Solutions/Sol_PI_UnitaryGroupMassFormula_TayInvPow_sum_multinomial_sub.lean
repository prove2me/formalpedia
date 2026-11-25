-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.TayInvPow.sum_multinomial_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:44:19.176901+00:00
-- url     : https://prove2.me/submissions/0f511591-501c-4b5e-b203-bb00cbf9bf8b

import Definitions.Def_Formalism_PeriodIntegrals_TayInvPow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TaylorInversePower_SumMultinomialSub

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
theorem _root_.solution (β : σ →₀ ℕ) (hβ : β ≠ 0) :
    ∑ p ∈ β.support, Nat.multinomial β.support (β - Finsupp.single p 1 : σ →₀ ℕ) =
      Nat.multinomial β.support β := by
  classical
  have hP : 0 < ∏ i ∈ β.support, (β i).factorial :=
    Finset.prod_pos (fun i _ => Nat.factorial_pos _)
  have key : ∀ p ∈ β.support, (∏ i ∈ β.support, (β i).factorial) *
      Nat.multinomial β.support (β - Finsupp.single p 1 : σ →₀ ℕ) =
        β p * (∑ i ∈ β.support, β i - 1).factorial := by
    intro p hp
    have hp' : β p ≠ 0 := Finsupp.mem_support_iff.1 hp
    have herase : ∀ i ∈ β.support.erase p, (β - Finsupp.single p 1 : σ →₀ ℕ) i = β i := by
      intro i hi
      have hne : p ≠ i := (Finset.ne_of_mem_erase hi).symm
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero]
    have hpp : (β - Finsupp.single p 1 : σ →₀ ℕ) p = β p - 1 := by
      rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
    have hsum : ∑ i ∈ β.support, (β - Finsupp.single p 1 : σ →₀ ℕ) i = ∑ i ∈ β.support, β i - 1 := by
      rw [← Finset.add_sum_erase β.support _ hp, ← Finset.add_sum_erase β.support _ hp,
        Finset.sum_congr rfl herase, hpp]
      have e : (∑ x ∈ β.support.erase p, β x) = (β.support.erase p).sum ⇑β := rfl
      omega
    have hprod : ∏ i ∈ β.support, (β i).factorial =
        β p * ∏ i ∈ β.support, ((β - Finsupp.single p 1 : σ →₀ ℕ) i).factorial := by
      rw [← Finset.mul_prod_erase β.support _ hp,
        ← Finset.mul_prod_erase β.support (fun i => ((β - Finsupp.single p 1 : σ →₀ ℕ) i).factorial) hp,
        Finset.prod_congr rfl (fun i hi => congrArg Nat.factorial (herase i hi)), hpp, ← mul_assoc,
        Nat.mul_factorial_pred hp']
    rw [hprod, mul_assoc, Nat.multinomial_spec, hsum]
  apply Nat.eq_of_mul_eq_mul_left hP
  rw [Finset.mul_sum, Finset.sum_congr rfl key, ← Finset.sum_mul, Nat.multinomial_spec]
  obtain ⟨p, hp⟩ := Finsupp.support_nonempty_iff.2 hβ
  have hpos : β p ≤ ∑ i ∈ β.support, β i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hp
  have hp' : β p ≠ 0 := Finsupp.mem_support_iff.1 hp
  exact Nat.mul_factorial_pred (by omega)
end PI.UnitaryGroupMassFormula.TayInvPow
