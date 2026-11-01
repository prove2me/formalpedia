-- Prove2me | solution 1 for OpenSearchSafety.leader_completeness
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:56:01.928777+00:00
-- url     : https://prove2.me/submissions/75b68d79-c698-47c9-95d0-d838616fada4

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

/-- **Leader completeness.** Every publication of a later term than a committed publication descends from it: a
cluster-manager of a later term always builds on the committed state (publications of the committed key's own term or of
older terms are not covered). -/
theorem solution {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (t : Nat) (v : Int) (hc : Committed W t v) (src : NodeId) (s : ClusterState V) (pt : Nat) (pv : Int)
    (hs : W.sent (.publishRequest src s pt pv)) (hlt : t < s.term) :
    Descends W t v s.term s.version := by
  exact inv_leader_completeness P hP W (reachable_inv P hP hes W hW) t v hc src s pt pv hs hlt
