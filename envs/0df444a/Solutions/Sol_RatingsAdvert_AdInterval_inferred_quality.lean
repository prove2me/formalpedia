-- Prove2me | solution 1 for RatingsAdvert.AdInterval.inferred_quality
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:25:15.667768+00:00
-- url     : https://prove2.me/submissions/d35f1f71-a1a8-42e0-bf79-95c8cc251cfb

import Mathlib
import Definitions.Def_RatingsAdvert_AdInterval_Model

open RatingsAdvert.AdInterval in
theorem solution (P : Params) (hβ : 0 < P.beta) (q z ze p1 q' : ℝ) :
    (mu1 P q' ze ze p1 = mu1 P q z ze p1 ↔ q' = (P.beta * q - P.tau * (z - ze)) / P.beta) ∧
      ((P.beta * q - P.tau * (z - ze)) / P.beta ∈ Set.Icc (0 : ℝ) 2 →
        qe P q z ze = (P.beta * q - P.tau * (z - ze)) / P.beta) := by
  refine ⟨?_, ?_⟩
  · rw [eq_div_iff hβ.ne']
    unfold mu1
    constructor
    · intro h; linear_combination h
    · intro h; linear_combination h
  · intro h
    unfold qe
    rw [max_eq_right h.1, min_eq_left h.2]
