-- Prove2me | solution 1 for ShorNonsmooth.Ellipsoid.saddle_field_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T09:54:39.039991+00:00
-- url     : https://prove2.me/submissions/8a2ff292-990d-4413-954c-f020746bec00

import Mathlib

theorem solution {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hconv : ∀ y, ConvexOn ℝ Set.univ (fun x => f x y))
    (hconc : ∀ x, ConcaveOn ℝ Set.univ (fun y => f x y))
    (gx : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n))
    (gy : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hgx : ∀ x y x', f x' y - f x y ≥ inner ℝ (gx x y) (x' - x))
    (hgy : ∀ x y y', f x y' - f x y ≤ inner ℝ (gy x y) (y' - y))
    (xstar : EuclideanSpace ℝ (Fin n)) (ystar : EuclideanSpace ℝ (Fin m))
    (hsaddle : ∀ x y, f xstar y ≤ f xstar ystar ∧ f xstar ystar ≤ f x ystar) :
    ∀ x y, 0 ≤ inner ℝ (gx x y) (x - xstar) + inner ℝ (-gy x y) (y - ystar) := by
  intro x y
  have h1 := hgx x y xstar
  have h2 := hgy x y ystar
  have h3 := hsaddle x y
  have e1 : inner ℝ (gx x y) (x - xstar) = - inner ℝ (gx x y) (xstar - x) := by
    rw [← inner_neg_right, neg_sub]
  have e2 : inner ℝ (-gy x y) (y - ystar) = inner ℝ (gy x y) (ystar - y) := by
    rw [inner_neg_left, ← inner_neg_right, neg_sub]
  rw [e1, e2]
  linarith [h3.1, h3.2]
