-- Prove2me | solution 1 for OpenSearchSafety.reachable_inv
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:55:31.366727+00:00
-- url     : https://prove2.me/submissions/c816611c-dfd5-4828-ba28-073f6b0cdd5c

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

open OpenSearchCoordination OpenSearchSafety

/-- **The invariant holds in every reachable cluster.** -/
theorem solution {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W) : Inv P W := by
  induction hW with
  | init W h => exact inv_init P W h
  | step W W' _ hs ih =>
    cases hs with
    | bootstrap n X s cs' hX hcontract hconf h =>
      exact inv_bootstrap P hP hes W ih n X s cs' hX hcontract hconf h
    | startJoin n src t cs' j hsrc h => exact inv_startJoin P hP hes W ih n src t cs' j hsrc h
    | join n j cs' b hsent hdest h => exact inv_join P hP hes W ih n j cs' b hsent hdest h
    | clientValue n s cs' p hcontract h => exact inv_clientValue P hP hes W ih n s cs' p hcontract h
    | publish n src s pt pv cs' r hsent h => exact inv_publish P hP hes W ih n src s pt pv cs' r hsent h
    | respond n src r cs' o hsent h =>
      cases o with
      | none => exact inv_respond P hP hes W ih n src r cs' none hsent h
      | some c => exact inv_respond P hP hes W ih n src r cs' (some c) hsent h
    | commit n c cs' hsent h => exact inv_commit P hP hes W ih n c cs' hsent h
    | restart n s' hn hs => exact inv_restart P hP hes W ih n s' hn hs
    | restartAny n t s' hn => exact inv_restartAny P hP hes W ih n t s' hn
