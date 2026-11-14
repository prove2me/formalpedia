-- Prove2me | solution 1 for StabilityDichotomies.Approximability.bernoulli_mask_restriction
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:26:46.531665+00:00
-- url     : https://prove2.me/submissions/5cee56b3-34e4-44e2-ac94-4d3df7802ebf

import Mathlib
noncomputable section
open scoped Classical BigOperators

private def maskEquiv {α β : Type} (e : α ≃ Option β) : (α → Bool) ≃ (Bool × (β → Bool)) where
  toFun x := (x (e.symm none), fun k => x (e.symm (some k)))
  invFun q := fun j => (e j).elim q.1 q.2
  left_inv := by
    intro x
    funext j
    cases h : e j with
    | none =>
      have hj : e.symm none = j := by apply e.injective; simpa using h.symm
      simp [h,hj]
    | some k =>
      have hj : e.symm (some k) = j := by apply e.injective; simpa using h.symm
      simp [h,hj]
  right_inv := by
    rintro ⟨b,y⟩
    simp

theorem solution {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ Option β) (p : ℝ) (g : (β → Bool) → ℝ) :
    (∑ x : α → Bool, (∏ j : α, if x j then p else 1-p) *
      g (fun k => x (e.symm (some k)))) =
    ∑ y : β → Bool, (∏ k : β, if y k then p else 1-p) * g y := by
  let E := maskEquiv e
  rw [← E.symm.sum_comp]
  rw [Fintype.sum_prod_type]
  have hw (b : Bool) (y : β → Bool) :
      (∏ j : α, if (E.symm (b,y)) j then p else 1-p) =
      (if b then p else 1-p) * ∏ k : β, if y k then p else 1-p := by
    rw [← e.symm.prod_comp (fun j : α => if (E.symm (b,y)) j then p else 1-p)]
    rw [Fintype.prod_option]
    simp [E, maskEquiv]
  simp_rw [hw]
  have hrest (b : Bool) (y : β → Bool) :
      (fun k => (E.symm (b,y)) (e.symm (some k))) = y := by
    funext k
    simp [E,maskEquiv]
  simp_rw [hrest]
  simp only [Fintype.sum_bool]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  ring
