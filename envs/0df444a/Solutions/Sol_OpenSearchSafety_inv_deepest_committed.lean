-- Prove2me | solution 1 for OpenSearchSafety.inv_deepest_committed
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:53:08.300537+00:00
-- url     : https://prove2.me/submissions/728a4d93-dca6-42b5-a197-7cf7405c449d

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

/-- Every key has a deepest committed ancestor-or-self (every committed ancestor-or-self of the key is an ancestor-or-self
of it), or no committed ancestor-or-self at all. -/
theorem solution {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (t : Nat) (v : Int) :
    (∃ dt dv, Committed W dt dv ∧ Descends W dt dv t v ∧
      ∀ et ev, Committed W et ev → Descends W et ev t v → Descends W et ev dt dv) ∨
    (∀ et ev, Committed W et ev → ¬ Descends W et ev t v) := by
  by_cases hpub : Published W t v
  · obtain ⟨src, s, pt, pv, hs, hst, hsv⟩ := hpub
    obtain ⟨v₀, hd⟩ := hinv.pub_rooted src s pt pv hs
    rw [hst, hsv] at hd
    clear hst hsv hs
    induction hd with
    | refl =>
      refine Or.inr (fun et ev hc hd' => ?_)
      have := (inv_committed_published P W hinv et ev hc).1
      rcases inv_descends_key P W hinv _ _ _ _ hd' with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
    | step t₁ v₁ t₂ v₂ _ hp ih =>
      obtain ⟨src', s', hs', hst', hsv'⟩ := hp
      have hsplit : ∀ ft fv, Descends W ft fv t₂ v₂ → (ft = t₂ ∧ fv = v₂) ∨ Descends W ft fv t₁ v₁ := by
        intro ft fv hf
        by_cases he : ft = t₂ ∧ fv = v₂
        · exact Or.inl he
        · exact Or.inr (inv_descends_parent P W hinv ft fv src' s' t₁ v₁ hs' (by rw [hst', hsv']; exact hf)
            (by rw [hst', hsv']; exact he))
      have hpar : Descends W t₁ v₁ t₂ v₂ := .step _ _ _ _ _ _ (.refl _ _) ⟨src', s', hs', hst', hsv'⟩
      by_cases hc₂ : Committed W t₂ v₂
      · exact Or.inl ⟨t₂, v₂, hc₂, .refl _ _, fun _ _ _ h => h⟩
      · have notself : ∀ et ev, Committed W et ev → ¬ (et = t₂ ∧ ev = v₂) := by
          rintro et ev hc ⟨rfl, rfl⟩; exact hc₂ hc
        rcases ih with ⟨dt, dv, h1, h2, h3⟩ | hnone
        · refine Or.inl ⟨dt, dv, h1, descends_trans W _ _ _ _ _ _ h2 hpar, fun et ev hc hd' => ?_⟩
          rcases hsplit et ev hd' with he | he
          · exact absurd he (notself et ev hc)
          · exact h3 et ev hc he
        · refine Or.inr (fun et ev hc hd' => ?_)
          rcases hsplit et ev hd' with he | he
          · exact notself et ev hc he
          · exact hnone et ev hc he
  · -- an unpublished key has no proper ancestor, and committed keys are published
    refine Or.inr (fun et ev hc hd' => ?_)
    cases hd' with
    | refl => exact hpub (inv_committed_published P W hinv _ _ hc).2
    | step t' v' _ _ _ hp =>
      obtain ⟨src, s, hs, h1, h2⟩ := hp
      exact hpub ⟨src, s, t', v', hs, h1, h2⟩
