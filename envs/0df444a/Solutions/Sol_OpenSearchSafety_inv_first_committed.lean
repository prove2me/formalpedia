-- Prove2me | solution 1 for OpenSearchSafety.inv_first_committed
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:53:08.762194+00:00
-- url     : https://prove2.me/submissions/3dd0df79-fcff-4fbe-845b-538cf03b8fbd

import Definitions.Def_OpenSearchSafety
import Theorems.Thm_OpenSearchSafety_descends_trans
import Theorems.Thm_OpenSearchSafety_inv_committed_published
import Theorems.Thm_OpenSearchSafety_inv_descends_key
import Theorems.Thm_OpenSearchSafety_inv_descends_parent

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

/-- Every committed key has a first committed ancestor-or-self: one with no committed proper ancestor. -/
theorem solution {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (t : Nat) (v : Int) (hc : Committed W t v) :
    ∃ et ev, Committed W et ev ∧ Descends W et ev t v ∧
      ∀ ft fv, Committed W ft fv → Descends W ft fv et ev → ft = et ∧ fv = ev := by
  obtain ⟨-, src, s, pt, pv, hs, hst, hsv⟩ := inv_committed_published P W hinv t v hc
  obtain ⟨v₀, hd⟩ := hinv.pub_rooted src s pt pv hs
  rw [hst, hsv] at hd
  suffices key : ∀ t' v', Descends W 0 v₀ t' v' → ∀ et ev, Committed W et ev → Descends W et ev t' v' →
      ∃ et ev, Committed W et ev ∧ Descends W et ev t' v' ∧
        ∀ ft fv, Committed W ft fv → Descends W ft fv et ev → ft = et ∧ fv = ev from
    key _ _ hd t v hc (.refl _ _)
  intro t' v' hd'
  induction hd' with
  | refl =>
    intro et ev hce hde
    exfalso
    have := (inv_committed_published P W hinv et ev hce).1
    rcases inv_descends_key P W hinv _ _ _ _ hde with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
  | step t₁ v₁ t₂ v₂ _ hp ih =>
    intro et ev hce hde
    obtain ⟨src', s', hs', hst', hsv'⟩ := hp
    have hsplit : ∀ ft fv, Descends W ft fv t₂ v₂ → (ft = t₂ ∧ fv = v₂) ∨ Descends W ft fv t₁ v₁ := by
      intro ft fv hf
      by_cases he : ft = t₂ ∧ fv = v₂
      · exact Or.inl he
      · exact Or.inr (inv_descends_parent P W hinv ft fv src' s' t₁ v₁ hs' (by rw [hst', hsv']; exact hf)
          (by rw [hst', hsv']; exact he))
    have hpar : Descends W t₁ v₁ t₂ v₂ := .step _ _ _ _ _ _ (.refl _ _) ⟨src', s', hs', hst', hsv'⟩
    by_cases hex : ∃ ft fv, Committed W ft fv ∧ Descends W ft fv t₁ v₁
    · obtain ⟨ft, fv, hf1, hf2⟩ := hex
      obtain ⟨e₁, e₂, k1, k2, k3⟩ := ih ft fv hf1 hf2
      exact ⟨e₁, e₂, k1, descends_trans W _ _ _ _ _ _ k2 hpar, k3⟩
    · have he : et = t₂ ∧ ev = v₂ := by
        rcases hsplit et ev hde with he | he
        · exact he
        · exact absurd ⟨et, ev, hce, he⟩ hex
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨et, ev, hce, .refl _ _, fun ft fv hf1 hf2 => ?_⟩
      rcases hsplit ft fv hf2 with h' | h'
      · exact h'
      · exact absurd ⟨ft, fv, hf1, h'⟩ hex
