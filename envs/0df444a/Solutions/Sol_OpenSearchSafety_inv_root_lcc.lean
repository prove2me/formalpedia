-- Prove2me | solution 1 for OpenSearchSafety.inv_root_lcc
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:53:10.410571+00:00
-- url     : https://prove2.me/submissions/81d8e7e1-36b3-44ec-bd3d-57a326d051fa

import Definitions.Def_OpenSearchSafety
import Theorems.Thm_OpenSearchSafety_descends_trans
import Theorems.Thm_OpenSearchSafety_inv_descends_key

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

/-- A publication without committed proper ancestor has a bootstrap configuration as last committed configuration: the
last committed configuration is copied from the parent unless the parent is committed. -/
theorem solution {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (src : NodeId) (s : ClusterState V) (pt : Nat) (pv : Int) (hs : W.sent (.publishRequest src s pt pv))
    (hroot : ∀ ft fv, Committed W ft fv → Descends W ft fv s.term s.version → ft = s.term ∧ fv = s.version) :
    P.initConfs s.lastCommittedConfiguration := by
  obtain ⟨v₀, hd⟩ := hinv.pub_rooted src s pt pv hs
  suffices key : ∀ t' v', Descends W 0 v₀ t' v' → ∀ src s pt pv, W.sent (.publishRequest src s pt pv) →
      s.term = t' → s.version = v' →
      (∀ ft fv, Committed W ft fv → Descends W ft fv t' v' → ft = t' ∧ fv = v') →
      P.initConfs s.lastCommittedConfiguration from
    key _ _ hd src s pt pv hs rfl rfl hroot
  intro t' v' hd'
  induction hd' with
  | refl =>
    intro src s pt pv hs ht _ _
    have := (hinv.pub_wf _ _ _ _ hs).2.1
    omega
  | step t₁ v₁ t₂ v₂ _ hp ih =>
    intro src s pt pv hs ht hv hroot
    obtain ⟨src₁, s₁, hs₁, h1, h2⟩ := hp
    obtain ⟨-, -, e3, e4⟩ := hinv.pub_unique _ _ _ _ _ _ _ _ hs hs₁ (ht.trans h1.symm) (hv.trans h2.symm)
    obtain ⟨-, -, -, hpv, hroot0⟩ := hinv.pub_wf _ _ _ _ hs
    by_cases h0 : pt = 0
    · exact hroot0 h0
    · obtain ⟨src₂, s₂, pt₂, pv₂, hs₂, h3, h4, hR1, -⟩ := hinv.pub_parent _ _ _ _ hs (by omega)
      -- the parent is a proper ancestor, hence not committed
      have hpar : Descends W pt pv t₂ v₂ := .step _ _ _ _ _ _ (.refl _ _) ⟨src, s, hs, ht, hv⟩
      have hnc : ¬ Committed W pt pv := by
        intro hc
        obtain ⟨-, hpv'⟩ := hroot pt pv hc hpar
        omega
      rw [hR1.resolve_right (fun h => hnc h.2)]
      apply ih src₂ s₂ pt₂ pv₂ hs₂ (h3.trans e3) (h4.trans e4)
      intro ft fv hfc hfd
      exfalso
      rw [← e3, ← e4] at hfd
      obtain ⟨-, hfv⟩ := hroot ft fv hfc (descends_trans W _ _ _ _ _ _ hfd hpar)
      rcases inv_descends_key P W hinv _ _ _ _ hfd with ⟨-, h5⟩ | ⟨-, h5⟩ <;> omega
