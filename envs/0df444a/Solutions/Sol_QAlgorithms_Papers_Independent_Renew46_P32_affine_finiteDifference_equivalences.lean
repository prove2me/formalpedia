-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P32.affine_finiteDifference_equivalences
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:08:38.391067+00:00
-- url     : https://prove2.me/submissions/063c07b1-44e4-446e-a556-bbe7a6eb9cd5

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P32

open QAlgorithms.Papers.Independent.Renew46.P32

open Set Filter Topology

universe u v

theorem g66b_lin2 {A : Type u} [AddCommGroup A] {B : Type u} [AddCommGroup B]
    (f : A → B) (x : A) (h : Fin 2 → A) :
    linearization f x 2 h = f (x + h 1 + h 0) - f (x + h 1) - (f (x + h 0) - f x) := rfl

section AlgebraicDefinitions

variable {K : Type u} [CommRing K]

variable {E : Type u} [AddCommGroup E] [Module K E]

variable {F : Type u} [AddCommGroup F] [Module K F]

theorem solution
    {A : Type u} [AddCommGroup A] {B : Type u} [AddCommGroup B]
    (f : A → B) :
    List.TFAE [
      (∃ a : A →+ B, ∃ b : B, ∀ x, f x = a x + b),
      (∀ x : A, ∀ h : Fin 2 → A, linearization f x 2 h = 0),
      (∀ h : Fin 2 → A, linearization f 0 2 h = 0),
      (∀ x u v : A, f (x + (u + v)) - f x =
        (f (x + u) - f x) + (f (x + v) - f x)),
      (∀ u v : A, f (u + v) - f 0 = (f u - f 0) + (f v - f 0))
    ] := by
  tfae_have 1 → 2 := by
    rintro ⟨a, b, hab⟩ x h
    rw [g66b_lin2, hab, hab, hab, hab]
    simp only [map_add]; abel
  tfae_have 2 → 3 := fun h => h 0
  tfae_have 3 → 5 := by
    intro h u v
    have := h ![u, v]
    rw [g66b_lin2] at this
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, zero_add] at this
    rw [add_comm u v]
    rw [sub_eq_zero] at this
    rw [show f (v + u) - f 0 = (f (v + u) - f v) + (f v - f 0) by abel, this]
  tfae_have 5 → 1 := by
    intro h
    refine ⟨AddMonoidHom.mk' (fun x => f x - f 0) h, f 0, fun x => ?_⟩
    simp
  tfae_have 1 → 4 := by
    rintro ⟨a, b, hab⟩ x u v
    simp only [hab, map_add]; abel
  tfae_have 4 → 5 := by
    intro h u v
    simpa using h 0 u v
  tfae_finish
