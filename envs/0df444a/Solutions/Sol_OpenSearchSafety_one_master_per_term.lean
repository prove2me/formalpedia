-- Prove2me | solution 1 for OpenSearchSafety.one_master_per_term
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:56:00.392317+00:00
-- url     : https://prove2.me/submissions/346b998d-7704-44a0-9905-28d80fa51e6a

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

/-- **One cluster-manager per term.** Two publications of the same term come from the same node. (OpenSearch's
randomized `CoordinationStateTestCluster.invariant()` checks this on random executions.) -/
theorem solution {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (a b : NodeId) (s s' : ClusterState V) (pt pt' : Nat) (pv pv' : Int)
    (h₁ : W.sent (.publishRequest a s pt pv)) (h₂ : W.sent (.publishRequest b s' pt' pv'))
    (ht : s.term = s'.term) : a = b := by
  have hinv := reachable_inv P hP hes W hW
  exact hinv.won_unique a b s.term ⟨(hinv.pub_wf _ _ _ _ h₁).1, Or.inr ⟨s, pt, pv, h₁, rfl⟩⟩
    ⟨(hinv.pub_wf _ _ _ _ h₂).1, Or.inr ⟨s', pt', pv', h₂, ht.symm⟩⟩
