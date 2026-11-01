-- Prove2me | solution 1 for OpenSearchSafety.inv_committed_comparable
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:54:30.537207+00:00
-- url     : https://prove2.me/submissions/741012c5-c2c7-4969-b7bc-e3fae159aa47

import Definitions.Def_OpenSearchSafety
import Theorems.Thm_OpenSearchSafety_inv_committed_published
import Theorems.Thm_OpenSearchSafety_inv_leader_completeness

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

/-- (S3) Committed keys are totally ordered by descent. -/
theorem solution {V : Type} (P : Params) (hP : P.InitCompatible) (W : Cluster V)
    (hinv : Inv P W) (t₁ t₂ : Nat) (v₁ v₂ : Int) (h₁ : Committed W t₁ v₁) (h₂ : Committed W t₂ v₂) :
    Descends W t₁ v₁ t₂ v₂ ∨ Descends W t₂ v₂ t₁ v₁ := by
  obtain ⟨-, src₁, s₁, pt₁, pv₁, hs₁, ht₁, hv₁⟩ := inv_committed_published P W hinv t₁ v₁ h₁
  obtain ⟨-, src₂, s₂, pt₂, pv₂, hs₂, ht₂, hv₂⟩ := inv_committed_published P W hinv t₂ v₂ h₂
  rcases Nat.lt_trichotomy t₁ t₂ with hlt | heq | hgt
  · left
    have := inv_leader_completeness P hP W hinv t₁ v₁ h₁ src₂ s₂ pt₂ pv₂ hs₂ (by rw [ht₂]; exact hlt)
    rw [ht₂, hv₂] at this
    exact this
  · rcases hinv.pub_same_term _ _ _ _ _ _ _ _ hs₁ hs₂ (ht₁.trans (heq.trans ht₂.symm)) with h | h
    · left; rw [ht₁, hv₁, ht₂, hv₂] at h; exact h
    · right; rw [ht₁, hv₁, ht₂, hv₂] at h; exact h
  · right
    have := inv_leader_completeness P hP W hinv t₂ v₂ h₂ src₁ s₁ pt₁ pv₁ hs₁ (by rw [ht₁]; exact hgt)
    rw [ht₁, hv₁] at this
    exact this
