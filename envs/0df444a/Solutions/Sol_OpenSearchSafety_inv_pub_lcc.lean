-- Prove2me | solution 1 for OpenSearchSafety.inv_pub_lcc
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:52:49.007859+00:00
-- url     : https://prove2.me/submissions/c474cecc-e51e-418e-86ff-a542c101327f

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

/-- (S5 for publications) Every publication's last committed configuration is a bootstrap configuration or the last
accepted configuration of a committed publication. -/
theorem solution {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (src : NodeId) (s : ClusterState V) (pt : Nat) (pv : Int) (hs : W.sent (.publishRequest src s pt pv)) :
    P.initConfs s.lastCommittedConfiguration ∨
    ∃ src' s' pt' pv', W.sent (.publishRequest src' s' pt' pv') ∧ Committed W s'.term s'.version ∧
      s'.lastAcceptedConfiguration = s.lastCommittedConfiguration := by
  obtain ⟨v₀, hd⟩ := hinv.pub_rooted src s pt pv hs
  suffices key : ∀ t' v', Descends W 0 v₀ t' v' → ∀ src s pt pv, W.sent (.publishRequest src s pt pv) →
      s.term = t' → s.version = v' → P.initConfs s.lastCommittedConfiguration ∨
      ∃ src' s' pt' pv', W.sent (.publishRequest src' s' pt' pv') ∧ Committed W s'.term s'.version ∧
        s'.lastAcceptedConfiguration = s.lastCommittedConfiguration from
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
    obtain ⟨-, -, -, -, hroot0⟩ := hinv.pub_wf _ _ _ _ hs
    by_cases h0 : pt = 0
    · exact Or.inl (hroot0 h0)
    · obtain ⟨src₂, s₂, pt₂, pv₂, hs₂, h3, h4, hR1, -⟩ := hinv.pub_parent _ _ _ _ hs (by omega)
      rcases hR1 with hl | ⟨hl, hc⟩
      · rw [hl]; exact ih src₂ s₂ pt₂ pv₂ hs₂ (h3.trans e3) (h4.trans e4)
      · exact Or.inr ⟨src₂, s₂, pt₂, pv₂, hs₂, by rw [h3, h4]; exact hc, hl.symm⟩
