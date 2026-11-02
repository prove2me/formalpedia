-- Prove2me | solution 1 for OpenSearchLiveness.prevote_then_stable_election
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T18:55:31.013433+00:00
-- url     : https://prove2.me/submissions/72e61d28-9753-4b72-b356-ef46519609e3

import Definitions.Def_OpenSearchCoordination
import Definitions.Def_OpenSearchSafety
import Definitions.Def_OpenSearchProgress
import Definitions.Def_OpenSearchPreVote
import Theorems.Thm_OpenSearchPreVote_round_entries
import Theorems.Thm_OpenSearchPreVote_votes_mem
import Theorems.Thm_OpenSearchProgress_election_possible

open OpenSearchCoordination OpenSearchSafety OpenSearchProgress OpenSearchPreVote

variable {V : Type}

private theorem liveness_send_node (W : Cluster V) (m : Message V) :
    (W.send m).node = W.node := rfl

private theorem liveness_set_node_self (W : Cluster V) (n : NodeId) (cs : CoordinationState V) :
    (W.set n cs).node n = cs := by
  simp [Cluster.set]

private theorem liveness_set_node_ne (W : Cluster V) (n m : NodeId) (cs : CoordinationState V)
    (h : m ≠ n) : (W.set n cs).node m = W.node m := by
  simp [Cluster.set, h]

theorem solution (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE)
    (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (hc : P.eligible c = true)
    (r : PreVotingRound V)
    (hr : RoundReachable ElectionStrategy.DEFAULT_INSTANCE
      (fun n resp => (W.node n.id).localNode = n ∧
        preVoteResponseOf (W.node n.id) = resp) r)
    (hstate : r.clusterState = (W.node c).lastAcceptedState)
    (hlocal : r.localNode = (W.node c).localNode)
    (hdn : ∀ p ∈ r.preVotesReceived, p.1 = P.dn p.1.id)
    (hquorum : r.votes.isQuorum r.clusterState.lastCommittedConfiguration = true ∧
      r.votes.isQuorum r.clusterState.lastAcceptedConfiguration = true)
    (maxTermSeen : Nat)
    (hseen : ∀ p ∈ r.preVotesReceived, p.2.currentTerm ≤ maxTermSeen) :
    ∃ W', ElectionExec P c (startElectionTerm (W.node c).currentTerm maxTermSeen)
        r.votes.nodes (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion W W' ∧
      (W'.node c).currentTerm = startElectionTerm (W.node c).currentTerm maxTermSeen ∧
      (W'.node c).electionWon = true := by
  classical
  have hent := (round_entries ElectionStrategy.DEFAULT_INSTANCE
    (fun n resp => (W.node n.id).localNode = n ∧ preVoteResponseOf (W.node n.id) = resp) r hr).1
  have hcur : ∀ p ∈ r.preVotesReceived, (W.node p.1.id).currentTerm = p.2.currentTerm ∧
      (W.node p.1.id).lastAcceptedTerm = p.2.lastAcceptedTerm ∧
      (W.node p.1.id).lastAcceptedVersionOrMetadataVersion = p.2.lastAcceptedVersion := by
    intro p hp
    obtain ⟨-, -, hresp⟩ := hent p hp
    exact ⟨by rw [← hresp]; rfl, by rw [← hresp]; rfl, by rw [← hresp]; rfl⟩
  have hQelig : ∀ q ∈ r.votes.nodes, P.eligible q = true := by
    intro q hq
    obtain ⟨p, hp, hpx, hcm⟩ := (votes_mem r q).1 hq
    have hcm' : p.1.isClusterManagerNode = true := hcm
    rw [hdn p hp, hpx] at hcm'
    exact hcm'
  have hterm : ∀ q, q = c ∨ q ∈ r.votes.nodes →
      (W.node q).currentTerm < startElectionTerm (W.node c).currentTerm maxTermSeen := by
    intro q hq
    rcases hq with rfl | hq
    · unfold startElectionTerm; omega
    · obtain ⟨p, hp, hpx, -⟩ := (votes_mem r q).1 hq
      have hle := hseen p hp
      have hcq := (hcur p hp).1
      rw [hpx] at hcq
      unfold startElectionTerm; omega
  have hfresh : ∀ q ∈ r.votes.nodes, (W.node q).lastAcceptedTerm < (W.node c).lastAcceptedTerm ∨
      ((W.node q).lastAcceptedTerm = (W.node c).lastAcceptedTerm ∧
        (W.node q).lastAcceptedVersionOrMetadataVersion ≤
          (W.node c).lastAcceptedVersionOrMetadataVersion) := by
    intro q hq
    obtain ⟨p, hp, hpx, -⟩ := (votes_mem r q).1 hq
    obtain ⟨hnf, -⟩ := hent p hp
    have hlat := (hcur p hp).2.1
    have hlav := (hcur p hp).2.2
    rw [hpx] at hlat hlav
    rw [hlat, hlav]
    unfold NoFresher at hnf
    rw [hstate] at hnf
    exact hnf
  have hquorum' : (W.node c).lastCommittedConfiguration.hasQuorum r.votes.nodes = true ∧
      (W.node c).lastAcceptedConfiguration.hasQuorum r.votes.nodes = true := by
    constructor
    · show (W.node c).lastAcceptedState.lastCommittedConfiguration.hasQuorum r.votes.nodes = true
      rw [← hstate]
      exact hquorum.1
    · show (W.node c).lastAcceptedState.lastAcceptedConfiguration.hasQuorum r.votes.nodes = true
      rw [← hstate]
      exact hquorum.2
  exact election_possible P hP hes W hW c _ _ hc hQelig hquorum' hterm hfresh
