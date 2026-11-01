-- Prove2me | solution 1 for OpenSearchSafety.committed_versions
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:56:36.463262+00:00
-- url     : https://prove2.me/submissions/920d6dea-305c-486d-a5c8-89a1e6d3030f

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
import Theorems.Thm_OpenSearchSafety_one_state_per_version
import Theorems.Thm_OpenSearchSafety_reachable_inv

open OpenSearchCoordination OpenSearchSafety

/-- **A committed version is committed once.** Two committed publications with the same version have the same term
(hence, by `one_state_per_version`, they are the same publication with the same cluster state); and committed versions
increase with the term. -/
theorem solution {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (t₁ t₂ : Nat) (v₁ v₂ : Int) (h₁ : Committed W t₁ v₁) (h₂ : Committed W t₂ v₂) :
    (v₁ = v₂ → t₁ = t₂) ∧ (t₁ < t₂ → v₁ < v₂) := by
  have hinv := reachable_inv P hP hes W hW
  constructor
  · intro hv
    rcases inv_committed_comparable P hP W hinv t₁ t₂ v₁ v₂ h₁ h₂ with h | h
    · rcases inv_descends_key P W hinv _ _ _ _ h with ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · omega
    · rcases inv_descends_key P W hinv _ _ _ _ h with ⟨h, -⟩ | ⟨-, h⟩
      · exact h.symm
      · omega
  · intro ht
    obtain ⟨-, src, s, pt, pv, hs, h1, h2⟩ := inv_committed_published P W hinv t₂ v₂ h₂
    have h := inv_leader_completeness P hP W hinv t₁ v₁ h₁ src s pt pv hs (by omega)
    rw [h1, h2] at h
    rcases inv_descends_key P W hinv _ _ _ _ h with ⟨h, -⟩ | ⟨-, h⟩
    · omega
    · exact h
