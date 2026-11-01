-- Prove2me | solution 1 for OpenSearchSafety.inv_leader_completeness
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:54:09.625989+00:00
-- url     : https://prove2.me/submissions/eae4b89b-f65b-4053-ba6a-8d3166797854

import Definitions.Def_OpenSearchSafety
import Theorems.Thm_OpenSearchSafety_descends_trans
import Theorems.Thm_OpenSearchSafety_inv_elc
import Theorems.Thm_OpenSearchSafety_inv_reign_first

open OpenSearchCoordination OpenSearchSafety

/-- Counting: an element satisfying both `p` and `q` is counted at most twice on the left and once on each side. -/
private theorem filter_length_add_le {α : Type} (L : List α) (p q : α → Bool) :
    (L.filter p).length + (L.filter q).length ≤ L.length + (L.filter (fun x => p x && q x)).length := by
  induction L with
  | nil => simp
  | cons y ys ih =>
    cases hp : p y <;> cases hq : q y <;> simp [hp, hq] <;> omega

/-- Two quorums of the same voting configuration share a member of the configuration. -/
private theorem quorum_intersect (c : VotingConfiguration) (a b : List NodeId)
    (ha : c.hasQuorum a = true) (hb : c.hasQuorum b = true) :
    ∃ x, x ∈ c.nodeIds ∧ x ∈ a ∧ x ∈ b := by
  simp only [VotingConfiguration.hasQuorum, decide_eq_true_eq] at ha hb
  have key := filter_length_add_le c.nodeIds (fun x => a.contains x) (fun x => b.contains x)
  have hpos : 0 < (c.nodeIds.filter (fun x => a.contains x && b.contains x)).length := by omega
  obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos hpos
  rw [List.mem_filter, Bool.and_eq_true, List.contains_iff_mem, List.contains_iff_mem] at hx
  exact ⟨x, hx.1, hx.2.1, hx.2.2⟩

/-- No configuration has a quorum of the empty list. -/
private theorem hasQuorum_nil (c : VotingConfiguration) : c.hasQuorum [] = false := by
  unfold VotingConfiguration.hasQuorum
  rw [decide_eq_false_iff_not]
  have : (c.nodeIds.filter (fun x => ([] : List NodeId).contains x)).length = 0 := by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]; simp
  omega

/-- (Leader completeness) Every publication of a later term descends from every committed key. -/
theorem solution {V : Type} (P : Params) (hP : P.InitCompatible) (W : Cluster V)
    (hinv : Inv P W) (t : Nat) (v : Int) (hc : Committed W t v) (src : NodeId) (s : ClusterState V) (pt : Nat)
    (pv : Int) (hs : W.sent (.publishRequest src s pt pv)) (hlt : t < s.term) :
    Descends W t v s.term s.version := by
  obtain ⟨L, F, pt', pv', hF, hFt, hFpt, hFd⟩ := inv_reign_first P W hinv src s pt pv hs
  obtain ⟨y, J, hrec⟩ := hinv.pub_election L F pt' pv' hF hFpt
  have h1 := inv_elc P hP W hinv L F.term pt' pv' F.lastCommittedConfiguration y J hrec t v hc
    (by rw [hFt]; exact hlt)
  exact descends_trans W _ _ _ _ _ _ (.step _ _ _ _ _ _ h1 ⟨L, F, hF, rfl, rfl⟩) hFd
