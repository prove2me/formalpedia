-- Prove2me | solution 1 for SuperPolyak.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:16:46.647672+00:00
-- url     : https://prove2.me/submissions/e3b91bd0-fccb-4fe4-919f-890a68168c1e

import Mathlib
import Definitions.Def_SuperPolyak_solutionSet

open SuperPolyak in
theorem solution {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d))) {δ' : ℝ} (hδ' : 0 < δ')
    {y x xhat : EuclideanSpace ℝ (Fin d)} (hy : y ∈ X) (hx : x ∈ Metric.ball y δ')
    (hxhat : xhat ∈ nearestPoints X x) :
    xhat ∈ Metric.ball y (2 * δ') := by
  rw [Metric.mem_ball, dist_eq_norm] at hx ⊢
  have h1 := hxhat.2 y hy
  have h2 : ‖y - x‖ = ‖x - y‖ := norm_sub_rev _ _
  have h3 : ‖xhat - y‖ ≤ ‖xhat - x‖ + ‖x - y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  linarith
