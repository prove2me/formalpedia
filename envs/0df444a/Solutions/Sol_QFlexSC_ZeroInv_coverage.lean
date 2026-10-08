-- Prove2me | solution 1 for QFlexSC.ZeroInv.coverage
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T03:26:19.748802+00:00
-- url     : https://prove2.me/submissions/2f723491-13b5-4cda-8656-e081fede4034

import Definitions.Def_QFlexSC_ZeroInv_Model

set_option autoImplicit false
open QFlexSC.ZeroInv

theorem solution (P : QFParams) (f : ℕ → ℕ → ℝ) (I₀ : ℝ) (r₀ : ℕ → ℝ) :
    ∀ t : ℕ, 1 ≤ t →
      (∀ j : ℕ, target P (f t) (projInvAt P I₀ r₀ f t j) j ≤ sched P I₀ r₀ f t j) ∧
        0 ≤ inv P I₀ r₀ f t := by
  intro t ht
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  constructor
  · intro j
    simp only [projInvAt, Nat.add_sub_cancel, sched_succ, mcStep, entry]
    exact le_max_left _ _
  · rw [inv_succ, sched_succ]
    simp only [mcStep, entry, target, proj, Acum]
    norm_num only [Finset.Icc_eq_empty_of_lt (by omega : 0 < 1), Finset.prod_empty,
      sub_self, add_zero, one_mul, div_one]
    have h := le_max_left (f (u + 1) 0 - inv P I₀ r₀ f u)
      ((1 - P.ωin (0 + 1)) * sched P I₀ r₀ f u (0 + 1))
    linarith

#print axioms solution
