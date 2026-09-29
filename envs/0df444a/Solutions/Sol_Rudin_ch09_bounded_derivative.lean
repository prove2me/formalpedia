-- Prove2me | solution 1 for Rudin.ch09_bounded_derivative
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:38:57.416643+00:00
-- url     : https://prove2.me/submissions/e96da36a-9852-46fd-b74a-cc87cf33f3aa

import Mathlib
open Filter Topology MeasureTheory


/-- Rudin, Theorem 9.19: if `f` is differentiable on a convex open set `E` with
`‖f'(x)‖ ≤ M` there, then `f` is Lipschitz with constant `M` on `E`; in particular a vanishing
derivative on a convex open set forces `f` to be constant. -/
theorem solution (n m : ℕ) (E : Set (EuclideanSpace ℝ (Fin n))) (hE : IsOpen E)
    (hconv : Convex ℝ E) (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (f' : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)))
    (hf : ∀ x ∈ E, HasFDerivAt f (f' x) x) (M : ℝ) (hM : ∀ x ∈ E, ‖f' x‖ ≤ M) :
    ∀ a ∈ E, ∀ b ∈ E, ‖f b - f a‖ ≤ M * ‖b - a‖ := by
  intro a ha b hb
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x hx => (hf x hx).hasFDerivWithinAt) hM hconv ha hb


#print axioms solution
