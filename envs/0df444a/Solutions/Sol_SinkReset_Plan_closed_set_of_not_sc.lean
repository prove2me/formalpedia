-- Prove2me | solution 1 for SinkReset.Plan.closed_set_of_not_sc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:51:44.634674+00:00
-- url     : https://prove2.me/submissions/f6da16de-0bbd-4cf6-a57c-1de42f311ec7

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
public import Theorems.Thm_SinkReset_Plan_act_append
public import Theorems.Thm_SinkReset_Plan_word_append
section
@[expose] public section
namespace SinkReset
namespace Plan
section Basic
variable {n : ℕ} [NeZero n] (A : Automaton n)
private theorem word_nil : A.IsWord [] := by simp [Automaton.IsWord]
end Basic
section Transport
variable {n m : ℕ} [NeZero n] [NeZero m]
variable (A : Automaton n) (B : Automaton m) (τ : Letter n → Letter m)
end Transport
private theorem closed_set_of_not_sc' {n : ℕ} [NeZero n] (A : Automaton n)
    (h : ¬ ∀ p q : Fin n, p ≠ 0 → q ≠ 0 → ∃ w, A.IsWord w ∧ act w p = q) :
    ∃ R : Finset (Fin n), 0 ∈ R ∧ 2 ≤ R.card ∧ R.card < n ∧
      ∀ a ∈ A.letters, ∀ q ∈ R, a q ∈ R := by
  classical
  simp only [not_forall] at h
  obtain ⟨p, q, hp, hq, hpq⟩ := h
  set R := Finset.univ.filter (fun x => x = 0 ∨ ∃ w, A.IsWord w ∧ act w p = x) with hR
  refine ⟨R, by simp [hR], ?_, ?_, ?_⟩
  · have hsub : ({0, p} : Finset (Fin n)) ⊆ R := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simp [hR]
      · simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inr ⟨[], word_nil A, rfl⟩
    calc 2 = ({0, p} : Finset (Fin n)).card := (Finset.card_pair (Ne.symm hp)).symm
      _ ≤ R.card := Finset.card_le_card hsub
  · have hqR : q ∉ R := by
      simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and, not_or]
      exact ⟨hq, fun ⟨w, hw, hwq⟩ => hpq ⟨w, hw, hwq⟩⟩
    have : R ⊂ Finset.univ := Finset.ssubset_univ_iff.2 fun h => hqR (h ▸ Finset.mem_univ q)
    simpa using Finset.card_lt_card this
  · intro a ha x hx
    simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with rfl | ⟨w, hw, rfl⟩
    · exact Or.inl (A.sink_fixed a ha)
    · refine Or.inr ⟨w ++ [a], (word_append A w [a]).2 ⟨hw, ?_⟩, ?_⟩
      · intro b hb
        simp only [List.mem_singleton] at hb
        exact hb ▸ ha
      · rw [act_append]; rfl
section Upper
variable {n k : ℕ} [NeZero n] (A : Automaton n)
end Upper
end Plan
end SinkReset
end
end

set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
namespace SinkReset.Plan
theorem _root_.solution {n : ℕ} [NeZero n] (A : Automaton n) (h : ¬ SC A) :
    ∃ R : Finset (Fin n), 0 ∈ R ∧ 2 ≤ R.card ∧ R.card < n ∧
      ∀ a ∈ A.letters, ∀ q ∈ R, a q ∈ R :=
  closed_set_of_not_sc' A h
end SinkReset.Plan
