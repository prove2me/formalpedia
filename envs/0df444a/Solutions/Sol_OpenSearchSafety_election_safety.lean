-- Prove2me | solution 1 for OpenSearchSafety.election_safety
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:56:04.221067+00:00
-- url     : https://prove2.me/submissions/5344c5b4-79dc-40cb-8557-ebcc97cb469d

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

/-- **Election safety.** Two nodes that hold a won election at the same moment (in the same cluster), in the same
current term, are the same node. -/
theorem solution {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (a b : NodeId) (ha : (W.node a).electionWon = true) (hb : (W.node b).electionWon = true)
    (ht : (W.node a).currentTerm = (W.node b).currentTerm) : a = b := by
  have hinv := reachable_inv P hP hes W hW
  have hb' := inv_won_of_electionWon P W hinv b hb
  rw [← ht] at hb'
  exact hinv.won_unique a b _ (inv_won_of_electionWon P W hinv a ha) hb'
