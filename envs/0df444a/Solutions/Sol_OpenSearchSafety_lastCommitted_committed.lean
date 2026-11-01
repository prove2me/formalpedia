-- Prove2me | solution 1 for OpenSearchSafety.lastCommitted_committed
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:56:05.341173+00:00
-- url     : https://prove2.me/submissions/8ce6642d-6c3c-4344-9fa8-b84ca665c19e

import Definitions.Def_OpenSearchSafety
import Theorems.Thm_OpenSearchSafety_inv_init
import Theorems.Thm_OpenSearchSafety_inv_bootstrap
import Theorems.Thm_OpenSearchSafety_inv_startJoin
import Theorems.Thm_OpenSearchSafety_inv_join
import Theorems.Thm_OpenSearchSafety_inv_clientValue
import Theorems.Thm_OpenSearchSafety_inv_publish
import Theorems.Thm_OpenSearchSafety_inv_respond
import Theorems.Thm_OpenSearchSafety_inv_commit
import Theorems.Thm_OpenSearchSafety_inv_restart
import Theorems.Thm_OpenSearchSafety_inv_restartAny
import Theorems.Thm_OpenSearchSafety_inv_descends_key
import Theorems.Thm_OpenSearchSafety_inv_committed_published
import Theorems.Thm_OpenSearchSafety_inv_won_of_electionWon
import Theorems.Thm_OpenSearchSafety_inv_pub_lcc
import Theorems.Thm_OpenSearchSafety_inv_leader_completeness
import Theorems.Thm_OpenSearchSafety_inv_committed_comparable
import Theorems.Thm_OpenSearchSafety_reachable_inv

open OpenSearchCoordination OpenSearchSafety

/-- **Committed configurations are committed.** The last committed configuration of every cluster-manager-eligible
node is empty (not bootstrapped), a bootstrap configuration, or the accepted configuration of a committed
publication. -/
theorem solution {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (n : NodeId) (hn : P.eligible n = true) :
    (W.node n).lastCommittedConfiguration = VotingConfiguration.EMPTY_CONFIG ∨
    P.initConfs (W.node n).lastCommittedConfiguration ∨
    ∃ src s pt pv, W.sent (.publishRequest src s pt pv) ∧ Committed W s.term s.version ∧
      s.lastAcceptedConfiguration = (W.node n).lastCommittedConfiguration := by
  have hinv := reachable_inv P hP hes W hW
  rcases hinv.accepted_realizes n hn with ⟨-, h0, -⟩ | ⟨-, -, hX⟩ |
      ⟨src, s, pt, pv, hs, h1, h2, -, h4 | ⟨h4, hc⟩⟩
  · exact Or.inl h0
  · exact Or.inr (Or.inl hX)
  · rcases inv_pub_lcc P W hinv src s pt pv hs with h | ⟨src', s', pt', pv', hs', hc', he⟩
    · rw [h4]; exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨src', s', pt', pv', hs', hc', he.trans h4.symm⟩)
  · exact Or.inr (Or.inr ⟨src, s, pt, pv, hs, by rw [h1, h2]; exact hc, h4.symm⟩)
