-- Prove2me | solution 1 for OpenSearchSafety.committed_linear
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:56:03.014405+00:00
-- url     : https://prove2.me/submissions/3c4381be-f926-4ac6-bec5-59875a55c1cc

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

/-- **Committed states never fork.** Any two committed publications are related by descent: the committed cluster
states form a single history. -/
theorem solution {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (t₁ t₂ : Nat) (v₁ v₂ : Int) (h₁ : Committed W t₁ v₁) (h₂ : Committed W t₂ v₂) :
    Descends W t₁ v₁ t₂ v₂ ∨ Descends W t₂ v₂ t₁ v₁ := by
  exact inv_committed_comparable P hP W (reachable_inv P hP hes W hW) t₁ t₂ v₁ v₂ h₁ h₂
