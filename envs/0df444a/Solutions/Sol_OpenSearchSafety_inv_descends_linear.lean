-- Prove2me | solution 1 for OpenSearchSafety.inv_descends_linear
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:52:46.696549+00:00
-- url     : https://prove2.me/submissions/4d85c8da-5405-419c-a358-503f02c06047

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

/-- The ancestors of a key are totally ordered by descent (a publication has a single parent). -/
theorem solution {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (t₁ t₂ t : Nat) (v₁ v₂ v : Int) (h₁ : Descends W t₁ v₁ t v) (h₂ : Descends W t₂ v₂ t v) :
    Descends W t₁ v₁ t₂ v₂ ∨ Descends W t₂ v₂ t₁ v₁ := by
  induction h₂ generalizing t₁ v₁ with
  | refl => exact Or.inl h₁
  | step t' v' t'' v'' h₂' hp ih =>
    cases h₁ with
    | refl => exact Or.inr (.step _ _ _ _ _ _ h₂' hp)
    | step t₀ v₀ _ _ h₁' hp₁ =>
      obtain ⟨src, s, hs, h1, h2⟩ := hp
      obtain ⟨src₁, s₁, hs₁, h3, h4⟩ := hp₁
      obtain ⟨-, -, rfl, rfl⟩ := hinv.pub_unique _ _ _ _ _ _ _ _ hs hs₁ (h1.trans h3.symm) (h2.trans h4.symm)
      exact ih _ _ h₁'
