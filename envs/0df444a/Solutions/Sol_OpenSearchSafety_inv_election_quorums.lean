-- Prove2me | solution 1 for OpenSearchSafety.inv_election_quorums
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:54:10.281411+00:00
-- url     : https://prove2.me/submissions/97412b58-4469-4cd2-a60b-f97a7d6bc912

import Definitions.Def_OpenSearchSafety
import Theorems.Thm_OpenSearchSafety_inv_descends_key
import Theorems.Thm_OpenSearchSafety_inv_elc
import Theorems.Thm_OpenSearchSafety_inv_pivot

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

/-- (ESL) Two election records of the same term share a voter: their bases have the same pivot (by `inv_elc`), whose
last accepted configuration both voter lists are quorums of, or both bases have no committed ancestor and the voter
lists are quorums of two bootstrap configurations (`P.InitCompatible`). -/
theorem solution {V : Type} (P : Params) (hP : P.InitCompatible) (W : Cluster V)
    (hinv : Inv P W) (t : Nat) (L₁ L₂ : NodeId) (bt₁ bt₂ : Nat) (bv₁ bv₂ : Int)
    (x₁ y₁ x₂ y₂ : VotingConfiguration) (J₁ J₂ : List NodeId)
    (h₁ : ElectionRecord P W L₁ t bt₁ bv₁ x₁ y₁ J₁) (h₂ : ElectionRecord P W L₂ t bt₂ bv₂ x₂ y₂ J₂) :
    ∃ m, m ∈ J₁ ∧ m ∈ J₂ := by
  have hanti : ∀ a b c d, Descends W a b c d → Descends W c d a b → a = c ∧ b = d := by
    intro a b c d e₁ e₂
    rcases inv_descends_key P W hinv _ _ _ _ e₁ with h | ⟨-, e₁'⟩
    · exact h
    · rcases inv_descends_key P W hinv _ _ _ _ e₂ with ⟨h, h'⟩ | ⟨-, e₂'⟩
      · exact ⟨h.symm, h'.symm⟩
      · omega
  obtain ⟨hlt₁, hr₁, hJ₁, hq₁x, hq₁y⟩ := id h₁
  obtain ⟨hlt₂, hr₂, hJ₂, hq₂x, hq₂y⟩ := id h₂
  -- a committed ancestor of a base of term < t has term < t
  have hlow : ∀ dt dv bt bv, Descends W dt dv bt bv → bt < t → dt < t := by
    intro dt dv bt bv hd hb
    rcases inv_descends_key P W hinv _ _ _ _ hd with ⟨h5, -⟩ | ⟨h5, -⟩ <;> omega
  rcases inv_pivot P W hinv bt₁ bv₁ x₁ y₁ hr₁ with ⟨srcD₁, sD₁, ptD₁, pvD₁, hD₁, hc₁, hd₁, hmax₁, hk₁⟩ |
      ⟨hnone₁, hX₁⟩ <;>
    rcases inv_pivot P W hinv bt₂ bv₂ x₂ y₂ hr₂ with ⟨srcD₂, sD₂, ptD₂, pvD₂, hD₂, hc₂, hd₂, hmax₂, hk₂⟩ |
      ⟨hnone₂, hX₂⟩
  · -- both bases have committed pivots: by election leader completeness, it is the same pivot
    have e12 := hmax₁ _ _ hc₂ (inv_elc P hP W hinv L₁ t bt₁ bv₁ x₁ y₁ J₁ h₁ _ _ hc₂ (hlow _ _ _ _ hd₂ hlt₂))
    have e21 := hmax₂ _ _ hc₁ (inv_elc P hP W hinv L₂ t bt₂ bv₂ x₂ y₂ J₂ h₂ _ _ hc₁ (hlow _ _ _ _ hd₁ hlt₁))
    obtain ⟨et, ev⟩ := hanti _ _ _ _ e12 e21
    have hs12 : sD₁ = sD₂ := (hinv.pub_unique _ _ _ _ _ _ _ _ hD₁ hD₂ et.symm ev.symm).2.1
    have q₁ : sD₁.lastAcceptedConfiguration.hasQuorum J₁ = true := by
      rcases hk₁ with h | h <;> rw [← h] <;> assumption
    have q₂ : sD₂.lastAcceptedConfiguration.hasQuorum J₂ = true := by
      rcases hk₂ with h | h <;> rw [← h] <;> assumption
    rw [hs12] at q₁
    obtain ⟨m, -, hm₁, hm₂⟩ := quorum_intersect _ _ _ q₁ q₂
    exact ⟨m, hm₁, hm₂⟩
  · exfalso
    exact hnone₂ _ _ hc₁ (inv_elc P hP W hinv L₂ t bt₂ bv₂ x₂ y₂ J₂ h₂ _ _ hc₁ (hlow _ _ _ _ hd₁ hlt₁))
  · exfalso
    exact hnone₁ _ _ hc₂ (inv_elc P hP W hinv L₁ t bt₁ bv₁ x₁ y₁ J₁ h₁ _ _ hc₂ (hlow _ _ _ _ hd₂ hlt₂))
  · -- neither base has a committed ancestor: two quorums of bootstrap configurations
    exact hP x₁ x₂ hX₁ hX₂ J₁ J₂ (fun x hx => (hJ₁ x hx).1) (fun x hx => (hJ₂ x hx).1) hq₁x hq₂x
