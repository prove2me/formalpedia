-- Prove2me | solution 1 for OpenSearchSafety.inv_commit_quorum_first
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:53:28.346199+00:00
-- url     : https://prove2.me/submissions/21936564-c82b-437d-8bc1-92b412b4683e

import Definitions.Def_OpenSearchSafety
import Theorems.Thm_OpenSearchSafety_inv_root_lcc

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

/-- (EC at a root) The publish responses to a committed key without committed proper ancestor include a quorum of a
bootstrap configuration. -/
theorem solution {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (ct : Nat) (cv : Int) (hc : Committed W ct cv)
    (hroot : ∀ ft fv, Committed W ft fv → Descends W ft fv ct cv → ft = ct ∧ fv = cv) :
    ∃ X A, P.initConfs X ∧ RespVoters P W ct cv A ∧ X.hasQuorum A = true := by
  obtain ⟨src, h⟩ := hc
  obtain ⟨src', s, pt, pv, hs, h1, h2, A, hA, -, h4⟩ := hinv.commit_quorum _ h
  have h1' : s.term = ct := h1
  have h2' : s.version = cv := h2
  rcases h4 with h4 | ⟨h4, -⟩
  · refine ⟨s.lastCommittedConfiguration, A, ?_, hA, h4⟩
    apply inv_root_lcc P W hinv src' s pt pv hs
    intro ft fv hfc hfd
    rw [h1', h2'] at hfd ⊢
    exact hroot ft fv hfc hfd
  · -- the parent is a committed proper ancestor
    exfalso
    have hd : Descends W pt pv ct cv := .step _ _ _ _ _ _ (.refl _ _) ⟨src', s, hs, h1', h2'⟩
    obtain ⟨-, hpv⟩ := hroot pt pv h4 hd
    have := (hinv.pub_wf _ _ _ _ hs).2.2.2.1
    omega
