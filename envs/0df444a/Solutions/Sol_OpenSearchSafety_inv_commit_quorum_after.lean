-- Prove2me | solution 1 for OpenSearchSafety.inv_commit_quorum_after
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:53:27.619099+00:00
-- url     : https://prove2.me/submissions/10dc72f8-c74f-4d69-8eed-426a386ae845

import Definitions.Def_OpenSearchSafety
import Theorems.Thm_OpenSearchSafety_inv_descends_parent
import Theorems.Thm_OpenSearchSafety_inv_lineage

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

/-- (EC) The publish responses to the committed key `c` closest above a publication `D` (no committed key strictly in
between) include a quorum of `D`'s last accepted configuration. -/
theorem solution {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (srcD : NodeId) (sD : ClusterState V) (ptD : Nat) (pvD : Int) (hD : W.sent (.publishRequest srcD sD ptD pvD))
    (ct : Nat) (cv : Int) (hc : Committed W ct cv) (h : Descends W sD.term sD.version ct cv)
    (hne : ¬ (sD.term = ct ∧ sD.version = cv))
    (hint : ∀ ft fv, Committed W ft fv → Descends W sD.term sD.version ft fv → Descends W ft fv ct cv →
      (ft = sD.term ∧ fv = sD.version) ∨ (ft = ct ∧ fv = cv)) :
    ∃ A, RespVoters P W ct cv A ∧ sD.lastAcceptedConfiguration.hasQuorum A = true := by
  obtain ⟨src, hc'⟩ := hc
  obtain ⟨srcC, sC, ptC, pvC, hC, h1, h2, A, hA, h3, h4⟩ := hinv.commit_quorum _ hc'
  have h1' : sC.term = ct := h1
  have h2' : sC.version = cv := h2
  refine ⟨A, hA, ?_⟩
  rcases h4 with h4 | ⟨h4, srcQ, sQ, ptQ, pvQ, hQ, h5, h6, h7⟩
  · -- the path summary from `D` to the committed key
    rcases inv_lineage P W hinv srcD srcC sD sC ptD ptC pvD pvC hD hC (by rw [h1', h2']; exact h)
      (by rw [h1', h2']; exact hne) (by rw [h1', h2']; exact hint) with hl | hl
    · rw [← hl]; exact h4
    · rw [← hl]; exact h3
  · -- (D1) the committed parent of the key lies between `D` and the key, so it is `D`
    have hdp : Descends W sD.term sD.version ptC pvC :=
      inv_descends_parent P W hinv _ _ srcC sC ptC pvC hC (by rw [h1', h2']; exact h) (by rw [h1', h2']; exact hne)
    have hpc : Descends W ptC pvC ct cv := .step _ _ _ _ _ _ (.refl _ _) ⟨srcC, sC, hC, h1', h2'⟩
    rcases hint ptC pvC h4 hdp hpc with ⟨e1, e2⟩ | ⟨-, e2⟩
    · obtain ⟨-, rfl, -, -⟩ := hinv.pub_unique _ _ _ _ _ _ _ _ hD hQ (e1.symm.trans h5.symm) (e2.symm.trans h6.symm)
      rw [h7]; exact h3
    · exfalso
      have := (hinv.pub_wf _ _ _ _ hC).2.2.2.1
      omega
