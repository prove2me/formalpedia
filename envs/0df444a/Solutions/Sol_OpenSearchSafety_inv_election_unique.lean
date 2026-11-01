-- Prove2me | solution 1 for OpenSearchSafety.inv_election_unique
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:54:31.231207+00:00
-- url     : https://prove2.me/submissions/7d7a61e1-4488-406a-aa57-5386fccc88a2

import Definitions.Def_OpenSearchSafety
import Theorems.Thm_OpenSearchSafety_inv_election_quorums

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

/-- Two election records of the same term are of the same candidate (their common voter sent one join per term). -/
theorem solution {V : Type} (P : Params) (hP : P.InitCompatible) (W : Cluster V)
    (hinv : Inv P W) (t : Nat) (L₁ L₂ : NodeId) (bt₁ bt₂ : Nat) (bv₁ bv₂ : Int)
    (x₁ y₁ x₂ y₂ : VotingConfiguration) (J₁ J₂ : List NodeId)
    (h₁ : ElectionRecord P W L₁ t bt₁ bv₁ x₁ y₁ J₁) (h₂ : ElectionRecord P W L₂ t bt₂ bv₂ x₂ y₂ J₂) :
    L₁ = L₂ := by
  obtain ⟨m, hm₁, hm₂⟩ := inv_election_quorums P hP W hinv t L₁ L₂ bt₁ bt₂ bv₁ bv₂ x₁ y₁ x₂ y₂ J₁ J₂ h₁ h₂
  obtain ⟨-, -, hJ₁, -, -⟩ := h₁
  obtain ⟨-, -, hJ₂, -, -⟩ := h₂
  obtain ⟨he, j₁, hj₁, hs₁, ht₁, hterm₁, -⟩ := hJ₁ m hm₁
  obtain ⟨-, j₂, hj₂, hs₂, ht₂, hterm₂, -⟩ := hJ₂ m hm₂
  have hjj := hinv.join_unique j₁ j₂ hj₁ hj₂ (by rw [hs₁]; exact he) (hs₁.trans hs₂.symm)
    (hterm₁.trans hterm₂.symm)
  rw [← ht₁, ← ht₂, hjj]
