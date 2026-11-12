-- Prove2me | solution 1 for TenChallenges.challenge_10
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:44:34.615272+00:00
-- url     : https://prove2.me/submissions/f9fe9363-de69-4f0c-9f1f-baaa8d69a11d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TenChallenges_challenge_10_r5
import Theorems.Thm_TenChallenges_challenge_10_locallyFinite
import Theorems.Thm_TenChallenges_challenge_10_largeClock_nonLocallyFinite

universe u v

private theorem wins_mono {V : Type u} (G : SimpleGraph V) {f : V → Option Bool}
    {α β : Ordinal.{v}} (hβα : β ≤ α) (h : PartitionerWins G f α) :
    PartitionerWins G f β := by
  rw [PartitionerWins] at h ⊢
  exact fun x γ hγ => h x γ (hγ.trans_le hβα)

/-- The reduction is conditional: the large-clock non-locally-finite case remains an assumption. -/
private theorem reduce_clock_cases
    (hfive : TenChallenges.statement_10.{u, v} 5)
    (hlocal : ∀ {V : Type u} [Countable V] (G : SimpleGraph V),
      (∀ x, (G.neighborSet x).Finite) → ∀ r : Ordinal.{v},
        PartitionerWins G (emptyPartition V) r)
    (hlarge : ∀ (r : Ordinal.{v}), 5 < r → ∀ {V : Type u} [Countable V]
      (G : SimpleGraph V), (¬ ∀ x, (G.neighborSet x).Finite) →
        PartitionerWins G (emptyPartition V) r) :
    ∀ r : Ordinal.{v}, TenChallenges.statement_10.{u, v} r := by
  intro r V hV G
  by_cases hr : r ≤ 5
  · exact wins_mono G hr (hfive hV G)
  · rcases Classical.em (∀ x, (G.neighborSet x).Finite) with hG | hG
    · exact @hlocal V hV G hG r
    · exact @hlarge r (lt_of_not_ge hr) V hV G hG

theorem solution : ∀ r : Ordinal.{v}, TenChallenges.statement_10.{u, v} r :=
  reduce_clock_cases TenChallenges.challenge_10_r5
    TenChallenges.challenge_10_locallyFinite
    TenChallenges.challenge_10_largeClock_nonLocallyFinite

#print axioms reduce_clock_cases
#print axioms solution
