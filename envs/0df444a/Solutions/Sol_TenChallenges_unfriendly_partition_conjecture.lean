-- Prove2me | solution 1 for TenChallenges.unfriendly_partition_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T03:25:05.085458+00:00
-- url     : https://prove2.me/submissions/0cf348ac-b34e-4dc2-b826-26f9bf4498af
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TenChallenges_unfriendly_partition_iff_all_clocks
import Theorems.Thm_TenChallenges_challenge_10

universe u

/-- Conditional reduction to the still-open scaled unfriendly-partition theorem. -/
theorem solution {V : Type u} [Countable V] (G : SimpleGraph V) :
    ∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x :=
  (TenChallenges.unfriendly_partition_iff_all_clocks G).2
    (fun α => TenChallenges.challenge_10.{u, u} α (inferInstance : Countable V) G)

#print axioms solution
