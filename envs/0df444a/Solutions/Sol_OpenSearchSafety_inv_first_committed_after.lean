-- Prove2me | solution 1 for OpenSearchSafety.inv_first_committed_after
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:53:09.314265+00:00
-- url     : https://prove2.me/submissions/e17d1e95-a9db-49bd-826e-61e4cae62bd8

import Definitions.Def_OpenSearchSafety
import Theorems.Thm_OpenSearchSafety_descends_trans
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

/-- Between a key `d` and a committed proper descendant `c` of it, there is a committed key `e` closest to `d`: every
committed key between `d` and `e` is `d` or `e`. -/
theorem solution {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (dt ct : Nat) (dv cv : Int) (h : Descends W dt dv ct cv) (hne : ¬ (dt = ct ∧ dv = cv))
    (hc : Committed W ct cv) :
    ∃ et ev, Committed W et ev ∧ Descends W dt dv et ev ∧ ¬ (dt = et ∧ dv = ev) ∧ Descends W et ev ct cv ∧
      ∀ ft fv, Committed W ft fv → Descends W dt dv ft fv → Descends W ft fv et ev →
        (ft = dt ∧ fv = dv) ∨ (ft = et ∧ fv = ev) := by
  -- antisymmetry of descent
  have hanti : ∀ a b c d, Descends W a b c d → Descends W c d a b → a = c ∧ b = d := by
    intro a b c d h₁ h₂
    rcases inv_descends_key P W hinv _ _ _ _ h₁ with h | ⟨-, h₁'⟩
    · exact h
    · rcases inv_descends_key P W hinv _ _ _ _ h₂ with ⟨h, h'⟩ | ⟨-, h₂'⟩
      · exact ⟨h.symm, h'.symm⟩
      · omega
  -- strengthened: from any committed key strictly after `d` on the way to `c'`
  suffices key : ∀ t' v', Descends W dt dv t' v' → ∀ et ev, Committed W et ev → Descends W dt dv et ev →
      ¬ (dt = et ∧ dv = ev) → Descends W et ev t' v' →
      ∃ et ev, Committed W et ev ∧ Descends W dt dv et ev ∧ ¬ (dt = et ∧ dv = ev) ∧ Descends W et ev t' v' ∧
        ∀ ft fv, Committed W ft fv → Descends W dt dv ft fv → Descends W ft fv et ev →
          (ft = dt ∧ fv = dv) ∨ (ft = et ∧ fv = ev) from
    key _ _ h ct cv hc h hne (.refl _ _)
  intro t' v' hd
  induction hd with
  | refl =>
    intro et ev _ h₁ hne' h₂
    exact absurd (hanti _ _ _ _ h₁ h₂) hne'
  | step t₁ v₁ t₂ v₂ hd₁ hp ih =>
    intro et ev hce h₁ hne' h₂
    obtain ⟨src, s, hs, hst, hsv⟩ := hp
    -- an ancestor-or-self of `(t₂, v₂)` is `(t₂, v₂)` or an ancestor-or-self of its parent
    have hsplit : ∀ ft fv, Descends W ft fv t₂ v₂ → (ft = t₂ ∧ fv = v₂) ∨ Descends W ft fv t₁ v₁ := by
      intro ft fv hf
      by_cases he : ft = t₂ ∧ fv = v₂
      · exact Or.inl he
      · exact Or.inr (inv_descends_parent P W hinv ft fv src s t₁ v₁ hs (by rw [hst, hsv]; exact hf)
          (by rw [hst, hsv]; exact he))
    have hpar : Descends W t₁ v₁ t₂ v₂ := .step _ _ _ _ _ _ (.refl _ _) ⟨src, s, hs, hst, hsv⟩
    by_cases hex : ∃ ft fv, Committed W ft fv ∧ Descends W dt dv ft fv ∧ ¬ (dt = ft ∧ dv = fv) ∧
        Descends W ft fv t₁ v₁
    · obtain ⟨ft, fv, hf1, hf2, hf3, hf4⟩ := hex
      obtain ⟨e₁, e₂, k1, k2, k3, k4, k5⟩ := ih ft fv hf1 hf2 hf3 hf4
      exact ⟨e₁, e₂, k1, k2, k3, descends_trans W _ _ _ _ _ _ k4 hpar, k5⟩
    · -- no committed key strictly between `d` and the parent: the committed key is `(t₂, v₂)` itself
      have hc₂ : et = t₂ ∧ ev = v₂ := by
        rcases hsplit et ev h₂ with he | he
        · exact he
        · exact absurd ⟨et, ev, hce, h₁, hne', he⟩ hex
      obtain ⟨rfl, rfl⟩ := hc₂
      refine ⟨et, ev, hce, h₁, hne', .refl _ _, ?_⟩
      intro ft fv hf1 hf2 hf3
      rcases hsplit ft fv hf3 with he | he
      · exact Or.inr he
      · by_cases hfd : dt = ft ∧ dv = fv
        · exact Or.inl ⟨hfd.1.symm, hfd.2.symm⟩
        · exact absurd ⟨ft, fv, hf1, hf2, hfd, he⟩ hex
