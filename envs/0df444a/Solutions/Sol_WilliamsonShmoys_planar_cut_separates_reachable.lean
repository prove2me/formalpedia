-- Prove2me | solution 1 for WilliamsonShmoys.planar_cut_separates_reachable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T06:42:55.630093+00:00
-- url     : https://prove2.me/submissions/7ad49b24-2640-41b9-b1ff-9bda1616bebf

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (A : Set V)
    (hCut : ∀ ⦃x y : V⦄, x ∈ A → y ∉ A → ¬ K.Adj x y)
    (u v : V) (hu : u ∈ A) (hv : v ∉ A) :
    ¬ K.Reachable u v := by
  rintro ⟨p⟩
  have key : ∀ (x w : V) (q : K.Walk x w), x ∈ A → w ∈ A := by
    intro x w q
    induction q with
    | nil => exact id
    | cons h _ ih =>
      intro hx
      apply ih
      by_contra hy
      exact hCut hx hy h
  exact hv (key u v p hu)
