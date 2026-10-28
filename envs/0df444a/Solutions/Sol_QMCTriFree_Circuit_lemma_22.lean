-- Prove2me | solution 1 for QMCTriFree.Circuit.lemma_22
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-25T23:13:10.068811+00:00
-- url     : https://prove2.me/submissions/d7e2a5c7-4404-4b1a-8f97-6fa96cbd6ff8

import Mathlib

set_option autoImplicit false

private theorem aux22 {ι : Type} [DecidableEq ι] (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (x : ι → ℝ) (S : Finset ι) (hx : ∀ k ∈ S, 0 ≤ x k) (h1 : ∑ k ∈ S, x k ≤ 1) :
    Real.sqrt (1 - β ^ 2 * (∑ k ∈ S, x k) ^ 2) ≤ ∏ k ∈ S, Real.sqrt (1 - β ^ 2 * x k ^ 2) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha] at h1 ⊢
    rw [Finset.prod_insert ha]
    have hxa : 0 ≤ x a := hx a (Finset.mem_insert_self _ _)
    have hS : 0 ≤ ∑ k ∈ S, x k := Finset.sum_nonneg (fun k hk => hx k (Finset.mem_insert_of_mem hk))
    have ih' := ih (fun k hk => hx k (Finset.mem_insert_of_mem hk)) (by linarith)
    set s := ∑ k ∈ S, x k
    have hxa1 : x a ≤ 1 := by linarith
    have hs1 : s ≤ 1 := by linarith
    have hb2 : β ^ 2 ≤ 1 := by nlinarith
    have hA : 0 ≤ 1 - β ^ 2 * x a ^ 2 := by
      have : x a ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg β, sq_nonneg (x a)]
    have hsq : Real.sqrt (1 - β ^ 2 * (x a + s) ^ 2)
        ≤ Real.sqrt ((1 - β ^ 2 * x a ^ 2) * (1 - β ^ 2 * s ^ 2)) := by
      apply Real.sqrt_le_sqrt
      nlinarith [mul_nonneg (mul_nonneg hxa hS) (sq_nonneg β),
        sq_nonneg (β ^ 2 * (x a * s))]
    rw [Real.sqrt_mul hA] at hsq
    calc _ ≤ _ := hsq
      _ ≤ _ := mul_le_mul_of_nonneg_left ih' (Real.sqrt_nonneg _)

theorem solution {ι : Type} (S : Finset ι) (x : ι → ℝ) (hx : ∀ k ∈ S, 0 ≤ x k)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hsum : ∑ k ∈ S, x k ≤ η)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    Real.sqrt (1 - β ^ 2 * η ^ 2) ≤ ∏ k ∈ S, Real.sqrt (1 - β ^ 2 * x k ^ 2) := by
  classical
  refine le_trans (Real.sqrt_le_sqrt ?_) (aux22 β hβ0 hβ1 x S hx (by linarith))
  have hS : 0 ≤ ∑ k ∈ S, x k := Finset.sum_nonneg hx
  have : (∑ k ∈ S, x k) ^ 2 ≤ η ^ 2 := by nlinarith
  nlinarith [sq_nonneg β]
