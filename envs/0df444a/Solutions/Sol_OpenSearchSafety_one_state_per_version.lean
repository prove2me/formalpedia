-- Prove2me | solution 1 for OpenSearchSafety.one_state_per_version
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:56:01.160169+00:00
-- url     : https://prove2.me/submissions/0bcf5f86-006b-4ecd-8cf4-b6273dcf7f02

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

/-- **One cluster state per term and version.** Two publications with the same term and version are the same
publication: same publisher, same cluster state, same parent. (Also checked by `CoordinationStateTestCluster`.) -/
theorem solution {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (a b : NodeId) (s s' : ClusterState V) (pt pt' : Nat) (pv pv' : Int)
    (h₁ : W.sent (.publishRequest a s pt pv)) (h₂ : W.sent (.publishRequest b s' pt' pv'))
    (ht : s.term = s'.term) (hv : s.version = s'.version) : a = b ∧ s = s' ∧ pt = pt' ∧ pv = pv' := by
  exact (reachable_inv P hP hes W hW).pub_unique _ _ _ _ _ _ _ _ h₁ h₂ ht hv
