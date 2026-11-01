-- Prove2me | solution 1 for OpenSearchSafety.commit_reachable
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:55:32.726229+00:00
-- url     : https://prove2.me/submissions/f251c132-dd7c-4f5f-bbe4-872f56548a7e

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

/-- Counting: an element satisfying both `p` and `q` is counted at most twice on the left and once on each side. -/
private theorem filter_length_add_le {α : Type} (L : List α) (p q : α → Bool) :
    (L.filter p).length + (L.filter q).length ≤ L.length + (L.filter (fun x => p x && q x)).length := by
  induction L with
  | nil => simp
  | cons y ys ih =>
    cases hp : p y <;> cases hq : q y <;> simp [hp, hq] <;> omega

/-- **Commits happen.** Some cluster with a compatible bootstrap configuration and the default strategy reaches a
commit of term 1, version 1: the hypotheses common to the safety theorems can be met together with a commit. Only this
one committed key is exhibited, not two distinct committed keys or a publication of a later term than a committed
key. -/
theorem solution : ∃ (P : Params) (W : Cluster Unit), P.InitCompatible ∧
    P.strategy = ElectionStrategy.DEFAULT_INSTANCE ∧ Reachable P W ∧ Committed W 1 1 := by
  -- one cluster-manager-eligible node, 0, bootstrapping alone
  let X₀ : VotingConfiguration := ⟨[0], List.Pairwise.cons (fun _ h => by cases h) .nil⟩
  let P : Params := ⟨fun _ => true, fun X => X = X₀, ElectionStrategy.DEFAULT_INSTANCE⟩
  have hP : P.InitCompatible := by
    intro X Y hX hY q₁ q₂ _ _ h₁ h₂
    have hX' : X = X₀ := hX
    have hY' : Y = X₀ := hY
    subst hX' hY'
    have m₁ : (0 : NodeId) ∈ q₁ := by
      by_cases hc : (0 : NodeId) ∈ q₁
      · exact hc
      · simp [VotingConfiguration.hasQuorum, X₀, hc] at h₁
    have m₂ : (0 : NodeId) ∈ q₂ := by
      by_cases hc : (0 : NodeId) ∈ q₂
      · exact hc
      · simp [VotingConfiguration.hasQuorum, X₀, hc] at h₂
    exact ⟨0, m₁, m₂⟩
  let s₀ : ClusterState Unit :=
    ⟨0, 0, 0, VotingConfiguration.EMPTY_CONFIG, VotingConfiguration.EMPTY_CONFIG, none, false, false, ()⟩
  let W₀ : Cluster Unit := ⟨fun n => CoordinationState.init (P.dn n) 0 s₀, fun _ => False⟩
  have r₀ : Reachable P W₀ := Reachable.init _ ⟨fun n => ⟨s₀, rfl, rfl, rfl, rfl⟩, fun _ h => h⟩
  -- 1. node 0 bootstraps with {0}
  let s₁ : ClusterState Unit := ⟨0, 0, 0, X₀, X₀, none, false, false, ()⟩
  have r₁ := Reachable.step _ _ r₀ (Step.bootstrap (P := P) W₀ 0 X₀ s₁ _ rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩ rfl)
  -- 2. node 0 starts an election in term 1 (a join from 0 to 0)
  have r₂ := Reachable.step _ _ r₁ (Step.startJoin (P := P) _ 0 0 1 _ _ rfl rfl)
  -- 3. node 0 handles its own join: it wins term 1
  have r₃ := Reachable.step _ _ r₂ (Step.join (P := P) _ 0 ⟨P.dn 0, P.dn 0, 1, 0, 0⟩ _ _ (Or.inr rfl) rfl rfl)
  -- 4. node 0 publishes version 1 of term 1
  let s₄ : ClusterState Unit := ⟨1, 1, 0, X₀, X₀, none, false, false, ()⟩
  have r₄ := Reachable.step _ _ r₃ (Step.clientValue (P := P) _ 0 s₄ _ _ rfl rfl)
  -- 5. node 0 accepts it
  have r₅ := Reachable.step _ _ r₄ (Step.publish (P := P) _ 0 0 s₄ 0 0 _ _ (Or.inr rfl) rfl)
  -- 6. node 0 handles its own response: a quorum of {0}, the commit is sent
  have r₆ := Reachable.step _ _ r₅ (Step.respond (P := P) _ 0 0 ⟨1, 1⟩ _ (some ⟨P.dn 0, 1, 1⟩) (Or.inr rfl) rfl)
  exact ⟨P, _, hP, rfl, r₆, ⟨P.dn 0, Or.inr rfl⟩⟩
