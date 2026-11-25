-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.TayInvPow.L_mul_F
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:02:51.95274+00:00
-- url     : https://prove2.me/submissions/e799571b-ac21-4914-adf8-34c66d231ee3

import Definitions.Def_Formalism_PeriodIntegrals_TayInvPow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TaylorInversePower_SumMultinomialSub
import Theorems.Thm_PI_UnitaryGroupMassFormula_TayInvPow_cf_rec
import Theorems.Thm_PI_UnitaryGroupMassFormula_TayInvPow_coeff_F

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
theorem _root_.solution (c : σ →₀ A) (s t : A) (hst : s * t = 1) (k : ℕ) :
    (C s + c.sum (fun p a => C a * X p)) * F c t (k + 1) = F c t k := by
  classical
  ext β
  rw [add_mul, map_add, coeff_C_mul, Finsupp.sum, Finset.sum_mul, map_sum]
  have hterm : ∀ p, coeff β (C (c p) * X p * F c t (k + 1)) =
      if Finsupp.single p 1 ≤ β then c p * cf c t (k + 1) (β - Finsupp.single p 1 : σ →₀ ℕ) else 0 := by
    intro p
    rw [mul_assoc, coeff_C_mul, X_def, coeff_monomial_mul, one_mul]
    split_ifs <;> simp [coeff_F]
  rw [Finset.sum_congr rfl (fun p _ => hterm p)]
  have h1 : ∑ p ∈ c.support,
      (if Finsupp.single p 1 ≤ β then c p * cf c t (k + 1) (β - Finsupp.single p 1 : σ →₀ ℕ) else 0) =
      ∑ p ∈ c.support ∪ β.support,
      (if Finsupp.single p 1 ≤ β then c p * cf c t (k + 1) (β - Finsupp.single p 1 : σ →₀ ℕ) else 0) :=
    Finset.sum_subset Finset.subset_union_left
      (fun p _ hp => by simp [Finsupp.notMem_support_iff.1 hp])
  have h2 : ∑ p ∈ β.support,
      (if Finsupp.single p 1 ≤ β then c p * cf c t (k + 1) (β - Finsupp.single p 1 : σ →₀ ℕ) else 0) =
      ∑ p ∈ c.support ∪ β.support,
      (if Finsupp.single p 1 ≤ β then c p * cf c t (k + 1) (β - Finsupp.single p 1 : σ →₀ ℕ) else 0) :=
    Finset.sum_subset Finset.subset_union_right (fun p _ hp => by
      rw [if_neg]
      intro h
      have h' := Finsupp.single_le_iff.1 h
      exact hp (Finsupp.mem_support_iff.2 (by omega)))
  have h3 : ∑ p ∈ β.support,
      (if Finsupp.single p 1 ≤ β then c p * cf c t (k + 1) (β - Finsupp.single p 1 : σ →₀ ℕ) else 0) =
      ∑ p ∈ β.support, c p * cf c t (k + 1) (β - Finsupp.single p 1 : σ →₀ ℕ) :=
    Finset.sum_congr rfl (fun p hp =>
      if_pos (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hp))))
  rw [h1, ← h2, h3, coeff_F, coeff_F]
  exact cf_rec c s t hst k β
end PI.UnitaryGroupMassFormula.TayInvPow
