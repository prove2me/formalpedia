-- Prove2me | solution 1 for PI.FinOrdRedOne.Core.eq_one_of_pow_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:05:05.482801+00:00
-- url     : https://prove2.me/submissions/d95de562-7df1-4ac5-aced-fa1e9f074485

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_EqOneOfIsOfFinOrder
import Theorems.Thm_PI_FinOrdRedOne_Core_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FinOrdRedOne PI.FinOrdRedOne.Core
open Matrix Finset
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
namespace PI.FinOrdRedOne.Core
theorem _root_.solution [IsDomain R] (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (hp0 : (p : R) ≠ 0) (hunit : ∀ l : ℕ, l.Prime → l ≠ p → IsUnit (l : R))
    (hsep : ∀ x : R, (∀ k : ℕ, (p : R) ^ k ∣ x) → x = 0)
    (A : Matrix n n R) (hA : PDvd (p : R) 1 (A - 1)) (l : ℕ) (hl : l.Prime) (hAl : A ^ l = 1) :
    A = 1 := by
  have key : ∀ a, 1 ≤ a → PDvd (p : R) a (A - 1) := by
    intro a ha
    induction a, ha using Nat.le_induction with
    | base => exact hA
    | succ a ha ih =>
      obtain ⟨X, hX⟩ := ih
      have hA' : A = 1 + (p : R) ^ a • X := by rw [← hX]; abel
      rw [hX]
      exact step p hp hp3 hp0 hunit l hl X a ha (hA' ▸ hAl)
  rw [← sub_eq_zero]
  ext i j
  rw [Matrix.zero_apply]
  apply hsep
  intro k
  obtain ⟨X, hX⟩ := key (k + 1) (by omega)
  rw [hX, Matrix.smul_apply, smul_eq_mul, pow_succ, mul_assoc]
  exact dvd_mul_right _ _
end PI.FinOrdRedOne.Core
