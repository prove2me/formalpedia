-- Prove2me | solution 1 for OpenSearchSafety.javaInvariant_reachable
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:56:04.773119+00:00
-- url     : https://prove2.me/submissions/1fe4cec2-2834-4aad-b9ce-fa6a46c791d3

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

/-- **The assertions of `CoordinationState.invariant()` never fail at a cluster-manager-eligible node.** At every
cluster-manager-eligible node of every reachable cluster, `invariant()` holds, although not every handler preserves it
on its own: `handlePublishRequest` can break it (`OpenSearchCoordination.javaInvariant_not_local`). -/
theorem solution {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (n : NodeId) (hn : P.eligible n = true) : (W.node n).javaInvariant P.strategy := by
  have hinv := reachable_inv P hP hes W hW
  unfold CoordinationState.javaInvariant
  refine ⟨hinv.term_le n hn, ?_, ?_, hinv.won_started n, ?_⟩
  · rw [hes]
    unfold CoordinationState.isElectionQuorum
    cases hw : (W.node n).electionWon
    · have := hinv.not_won_no_quorum n hw
      simp only [ElectionStrategy.DEFAULT_INSTANCE, Bool.and_true]
      cases h1 : (W.node n).joinVotes.isQuorum (W.node n).lastCommittedConfiguration <;>
        cases h2 : (W.node n).joinVotes.isQuorum (W.node n).lastAcceptedConfiguration <;> simp_all
    · obtain ⟨h1, h2⟩ := hinv.won_quorum n hw
      simp [h1, h2, ElectionStrategy.DEFAULT_INSTANCE]
  · cases hw : (W.node n).electionWon
    · simpa using (hinv.idle_of_not_won n hw).1
    · simp only [if_true]
      by_cases he : (W.node n).lastPublishedVersion = (W.node n).lastAcceptedVersion
      · omega
      · obtain ⟨s, hs, -, hv, -⟩ := hinv.leader_inflight n hw he
        have := (hinv.pub_wf _ _ _ _ hs).2.2.2.1
        omega
  · cases hw : (W.node n).electionWon
    · left; rw [(hinv.idle_of_not_won n hw).2]; rfl
    · right; rfl
