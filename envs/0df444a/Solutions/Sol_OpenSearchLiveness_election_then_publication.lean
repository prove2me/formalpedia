-- Prove2me | solution 1 for OpenSearchLiveness.election_then_publication
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T18:55:51.386344+00:00
-- url     : https://prove2.me/submissions/e1c5d8a1-a954-46fc-b37f-2634412b6204

import Definitions.Def_OpenSearchCoordination
import Definitions.Def_OpenSearchSafety
import Definitions.Def_OpenSearchProgress
import Definitions.Def_OpenSearchPreVote
import Theorems.Thm_OpenSearchProgress_publication_possible

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
    (c : NodeId) (t : Nat) (Q : List NodeId)
    (hQ : ∀ q ∈ Q, P.eligible q = true)
    (hwon : (W.node c).electionWon = true) (hct : (W.node c).currentTerm = t)
    (s : ClusterState V) (cs' : CoordinationState V) (p : PublishRequest V)
    (hcv : (W.node c).handleClientValue s = .ok (cs', p))
    (hcontract : (W.node c).clientValueContract s)
    (hfields : cs'.electionWon = (W.node c).electionWon ∧
      cs'.currentTerm = (W.node c).currentTerm ∧
      cs'.lastCommittedConfiguration = (W.node c).lastCommittedConfiguration ∧
      cs'.lastAcceptedConfiguration = (W.node c).lastAcceptedConfiguration ∧
      cs'.lastPublishedVersion = s.version ∧ cs'.publishVotes.nodes = [])
    (hpacc : p.acceptedState = s)
    (hst : s.term = t)
    (hquorum : (W.node c).lastCommittedConfiguration.hasQuorum Q = true ∧
      (W.node c).lastAcceptedConfiguration.hasQuorum Q = true ∧
      s.lastCommittedConfiguration.hasQuorum Q = true ∧
      s.lastAcceptedConfiguration.hasQuorum Q = true)
    (hterm : ∀ q ∈ Q, (W.node q).currentTerm ≤ t) :
    ∃ W', PublicationExec P c t Q
        ((W.set c cs').send (.publishRequest c p.acceptedState
          (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion)) W' ∧
      Committed W' t p.acceptedState.version := by
  generalize hW''def : (W.set c cs').send (.publishRequest c p.acceptedState
    (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion) = W''
  -- Abbreviation for the record-update facts, in the order of `hfields`.
  have hspec : cs'.electionWon = (W.node c).electionWon ∧
      cs'.currentTerm = (W.node c).currentTerm ∧
      cs'.lastCommittedConfiguration = (W.node c).lastCommittedConfiguration ∧
      cs'.lastAcceptedConfiguration = (W.node c).lastAcceptedConfiguration ∧
      cs'.lastPublishedVersion = s.version ∧ cs'.publishVotes.nodes = [] ∧
      p.acceptedState = s := ⟨hfields.1, hfields.2.1, hfields.2.2.1, hfields.2.2.2.1,
        hfields.2.2.2.2.1, hfields.2.2.2.2.2, hpacc⟩
  have hW'' : Reachable P W'' := by
    rw [← hW''def]
    exact Reachable.step _ _ hW (Step.clientValue W c s cs' p hcontract hcv)
  have hwon'' : (W''.node c).electionWon = true := by
    rw [← hW''def, liveness_send_node, liveness_set_node_self, hspec.1, hwon]
  have hct'' : (W''.node c).currentTerm = t := by
    rw [← hW''def, liveness_send_node, liveness_set_node_self, hspec.2.1, hct]
  have hs'' : W''.sent (.publishRequest c p.acceptedState
      (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion) := by
    rw [← hW''def]
    simp [Cluster.send]
  have hst'' : p.acceptedState.term = t := by
    rw [hspec.2.2.2.2.2.2]
    exact hst
  have hsv'' : p.acceptedState.version = (W''.node c).lastPublishedVersion := by
    rw [← hW''def, liveness_send_node, liveness_set_node_self, hspec.2.2.2.2.1, hspec.2.2.2.2.2.2]
  have hquorum'' : (W''.node c).lastCommittedConfiguration.hasQuorum Q = true ∧
      (W''.node c).lastAcceptedConfiguration.hasQuorum Q = true ∧
      p.acceptedState.lastCommittedConfiguration.hasQuorum Q = true ∧
      p.acceptedState.lastAcceptedConfiguration.hasQuorum Q = true := by
    rw [← hW''def, liveness_send_node, liveness_set_node_self, hspec.2.2.1, hspec.2.2.2.1,
      hspec.2.2.2.2.2.2]
    exact hquorum
  have hterm'' : ∀ q ∈ Q, (W''.node q).currentTerm ≤ t := by
    intro q hq
    by_cases hqc : q = c
    · subst hqc
      simp [← hW''def, liveness_send_node, liveness_set_node_self, hspec.2.1, hct]
    · rw [← hW''def, liveness_send_node, liveness_set_node_ne _ _ _ _ hqc]
      exact hterm q hq
  rw [← hW''def] at hwon'' hct'' hs'' hsv'' hquorum'' hterm'' hW''
  exact hW''def ▸ publication_possible P hP hes _ hW'' c t Q hQ hwon'' hct''
    p.acceptedState (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion
    hs'' hst'' hsv'' hquorum'' hterm''
