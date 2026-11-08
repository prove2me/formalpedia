-- Prove2me | solution 1 for SparseHistComm.posterior_list_card_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T03:58:01.268224+00:00
-- url     : https://prove2.me/submissions/a0768a08-ede0-4fe6-b180-1f60d66b2880

import Mathlib
import Definitions.Def_SparseHistComm_Protocol
import Definitions.Def_SparseHistComm_msgMass
import Definitions.Def_SparseHistComm_post
import Definitions.Def_SparseHistComm_postList

open SparseHistComm in
theorem solution (n k d : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkd : k ≤ d) (hd : 2 ≤ d)
    (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (P : Protocol n d) (i : Fin n) (r : P.Ω) (m : List Bool) :
    τ * (postList P k τ i r m).card ≤ ∑ a ∈ postList P k τ i r m, post P k i r m a ∧
    ∑ a ∈ postList P k τ i r m, post P k i r m a ≤ ∑ a, post P k i r m a ∧
    ∑ a, post P k i r m a ≤ k ∧
    (0 < msgMass P k i r m → ∑ a, post P k i r m a = k) ∧
    ((postList P k τ i r m).card : ℝ) ≤ k / τ := by
  have hw : ∀ x, 0 ≤ (prior d k).toReal * (P.enc i r x m).toReal := fun x =>
    mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hM0 : 0 ≤ msgMass P k i r m := by
    unfold msgMass; exact Finset.sum_nonneg fun x _ => hw x
  have hpost0 : ∀ a, 0 ≤ post P k i r m a := by
    intro a; unfold post
    exact div_nonneg (Finset.sum_nonneg fun x _ => hw x) hM0
  have hnum : ∑ a : Fin d, ∑ x ∈ ((Finset.univ : Finset (Fin d)).powersetCard k).filter
      (fun x => a ∈ x), (prior d k).toReal * (P.enc i r x m).toReal = k * msgMass P k i r m := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    unfold msgMass
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
      (Finset.mem_powersetCard.mp hx).2]
  have hsum : ∑ a, post P k i r m a = k * msgMass P k i r m / msgMass P k i r m := by
    unfold post
    rw [← Finset.sum_div, hnum]
  have h3 : ∑ a, post P k i r m a ≤ k := by
    rw [hsum]
    rcases hM0.lt_or_eq with h | h
    · rw [mul_div_assoc, div_self h.ne', mul_one]
    · rw [← h, div_zero]; positivity
  have h4 : 0 < msgMass P k i r m → ∑ a, post P k i r m a = k := by
    intro h; rw [hsum, mul_div_assoc, div_self h.ne', mul_one]
  have h1 : τ * (postList P k τ i r m).card ≤ ∑ a ∈ postList P k τ i r m, post P k i r m a := by
    have := Finset.card_nsmul_le_sum (postList P k τ i r m) (post P k i r m) τ (by
      intro a ha
      unfold postList at ha
      exact (Finset.mem_filter.mp ha).2.le)
    rw [nsmul_eq_mul] at this
    linarith
  have h2 : ∑ a ∈ postList P k τ i r m, post P k i r m a ≤ ∑ a, post P k i r m a :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ => hpost0 a)
  refine ⟨h1, h2, h3, h4, ?_⟩
  rw [le_div_iff₀ hτ0]
  linarith
