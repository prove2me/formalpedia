-- Prove2me | solution 1 for OpenSearchSafety.inv_reign_first
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:52:47.269749+00:00
-- url     : https://prove2.me/submissions/f0c6b8be-0eb8-434e-80fb-690dcefbfcd4

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

/-- Every publication descends from a first publication of its term: one whose parent is of an older term. -/
theorem solution {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (src : NodeId) (s : ClusterState V) (pt : Nat) (pv : Int) (hs : W.sent (.publishRequest src s pt pv)) :
    ∃ src' s' pt' pv', W.sent (.publishRequest src' s' pt' pv') ∧ s'.term = s.term ∧ pt' < s'.term ∧
      Descends W s'.term s'.version s.term s.version := by
  obtain ⟨v₀, hd⟩ := hinv.pub_rooted src s pt pv hs
  suffices key : ∀ t' v', Descends W 0 v₀ t' v' → ∀ src s pt pv, W.sent (.publishRequest src s pt pv) →
      s.term = t' → s.version = v' → ∃ src' s' pt' pv', W.sent (.publishRequest src' s' pt' pv') ∧
        s'.term = t' ∧ pt' < s'.term ∧ Descends W s'.term s'.version t' v' from
    key _ _ hd src s pt pv hs rfl rfl
  intro t' v' hd'
  induction hd' with
  | refl =>
    intro src s pt pv hs ht _
    have := (hinv.pub_wf _ _ _ _ hs).2.1
    omega
  | step t₁ v₁ t₂ v₂ _ hp ih =>
    intro src s pt pv hs ht hv
    obtain ⟨src₁, s₁, hs₁, h1, h2⟩ := hp
    obtain ⟨-, -, e3, e4⟩ := hinv.pub_unique _ _ _ _ _ _ _ _ hs hs₁ (ht.trans h1.symm) (hv.trans h2.symm)
    obtain ⟨-, hpos, hle, -, -⟩ := hinv.pub_wf _ _ _ _ hs
    by_cases hlt : pt < s.term
    · exact ⟨src, s, pt, pv, hs, ht, hlt, by rw [ht, hv]; exact .refl _ _⟩
    · obtain ⟨src₂, s₂, pt₂, pv₂, hs₂, h3, h4, -⟩ := hinv.pub_parent _ _ _ _ hs (by omega)
      obtain ⟨src', s', pt', pv', h5, h6, h7, h8⟩ := ih src₂ s₂ pt₂ pv₂ hs₂ (h3.trans e3) (h4.trans e4)
      refine ⟨src', s', pt', pv', h5, by omega, h7, .step _ _ _ _ _ _ h8 ⟨src₁, s₁, hs₁, h1, h2⟩⟩
