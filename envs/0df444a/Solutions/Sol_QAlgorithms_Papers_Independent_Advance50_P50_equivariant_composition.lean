-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P50.equivariant_composition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T12:55:24.468722+00:00
-- url     : https://prove2.me/submissions/1929b388-2599-40cf-9ed9-050605f8dcf5

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P50

open QAlgorithms.Papers.Independent.Advance50.P50

theorem s110_eqc_aux {G : Type*} [Group G] {A : ℕ → Type*}
    (action : ∀ j, G → A j → A j) (M : ℕ) (f : ∀ j, A j → A (j+1))
    (hequiv : ∀ j, j < M → ∀ g x, f j (action j g x) = action (j+1) g (f j x)) :
    ∀ m, m ≤ M → ∀ g x, composeLayers f m (action 0 g x) = action m g (composeLayers f m x) := by
  intro m
  induction m with
  | zero => intro _ g x; rfl
  | succ m ih =>
    intro hm g x
    show f m (composeLayers f m (action 0 g x)) = action (m+1) g (f m (composeLayers f m x))
    rw [ih (by omega) g x, hequiv m (by omega)]

theorem solution {G : Type*} [Group G] {A : ℕ → Type*} {B : Type*}
    (action : ∀ j, G → A j → A j)
    (haction : (∀ j x, action j 1 x = x) ∧
      ∀ j g h x, action j (g*h) x = action j g (action j h x))
    (M : ℕ) (f : ∀ j, A j → A (j+1)) (q : A M → B)
    (hequiv : ∀ j, j < M → ∀ g x, f j (action j g x) = action (j+1) g (f j x))
    (hfinal : ∀ g x, q (action M g x) = q x) :
    ∀ g x, q (composeLayers f M (action 0 g x)) = q (composeLayers f M x) := by
  intro g x
  rw [s110_eqc_aux action M f hequiv M le_rfl g x, hfinal]
