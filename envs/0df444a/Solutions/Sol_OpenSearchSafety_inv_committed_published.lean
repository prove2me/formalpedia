-- Prove2me | solution 1 for OpenSearchSafety.inv_committed_published
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:52:47.84957+00:00
-- url     : https://prove2.me/submissions/50d41bda-d37a-4789-b17d-997cdb1712c9

import Definitions.Def_OpenSearchSafety

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

/-- Every committed key is the key of a publication, of term ≥ 1. -/
theorem solution {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (t : Nat) (v : Int) (h : Committed W t v) :
    1 ≤ t ∧ ∃ src s pt pv, W.sent (.publishRequest src s pt pv) ∧ s.term = t ∧ s.version = v := by
  obtain ⟨src, h⟩ := h
  obtain ⟨src', s, pt, pv, hs, h1, h2, -⟩ := hinv.commit_quorum _ h
  obtain ⟨-, hpos, -⟩ := hinv.pub_wf _ _ _ _ hs
  have h1' : s.term = t := h1
  exact ⟨by omega, src', s, pt, pv, hs, h1', h2⟩
