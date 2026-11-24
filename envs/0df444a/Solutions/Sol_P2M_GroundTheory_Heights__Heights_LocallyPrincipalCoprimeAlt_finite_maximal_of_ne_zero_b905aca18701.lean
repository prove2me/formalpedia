-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_finite_maximal_of_ne_zero_b905aca18701
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T04:27:56.705885+00:00
-- url     : https://prove2.me/submissions/c1dc628f-f055-4575-acc6-2c003d2bdccb

import Mathlib
variable {L : Type} [Field L]


theorem solution [CharZero L] (B : Subring L) [Module.Finite ℤ B] {s : B} (hs : s ≠ 0) :
    Set.Finite {m : Ideal B | m.IsMaximal ∧ s ∈ m} := by
  exact (Ring.HasFiniteQuotients.finite_setOfPred_mem s hs).subset (fun _ hm => hm.2)
