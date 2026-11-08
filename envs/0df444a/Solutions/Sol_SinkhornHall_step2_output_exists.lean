-- Prove2me | solution 1 for SinkhornHall.step2_output_exists
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:45:05.82948+00:00
-- url     : https://prove2.me/submissions/c1e11c53-ae9d-4685-82a2-212f703b3ffe

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis

open Finset

open SinkhornHall in
theorem solution {n : ℕ} (hn : 0 < n) (x y : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (hy : ∀ j, 0 < y j) :
    ∃ X : Finset (Fin n), IsStep2Output x y X := by
  set σ := Tuple.sort (fun i => -x i) with hσdef
  set τ := Tuple.sort y with hτdef
  have hσ : Antitone (x ∘ σ) := by
    intro a b hab
    have := Tuple.monotone_sort (fun i => -x i) hab
    simp only [Function.comp] at this ⊢
    linarith
  have hτ : Monotone (y ∘ τ) := Tuple.monotone_sort y
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun t => x (σ t) * y (τ t)) hne
  refine ⟨_, σ, τ, k, hσ, hτ, ?_, rfl⟩
  have e1 : ∏ i, x i = ∏ t, x (σ t) := (Equiv.prod_comp σ x).symm
  have e2 : ∏ j, y j = ∏ t, y (τ t) := (Equiv.prod_comp τ y).symm
  calc (∏ i, x i) * (∏ j, y j) = ∏ t, (x (σ t) * y (τ t)) := by
        rw [e1, e2, Finset.prod_mul_distrib]
    _ ≤ ∏ _t : Fin n, (x (σ k) * y (τ k)) :=
        Finset.prod_le_prod (fun t _ => (mul_pos (hx _) (hy _)).le)
          (fun t _ => hk t (Finset.mem_univ t))
    _ = (x (σ k) * y (τ k)) ^ n := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
