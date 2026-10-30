-- Prove2me | solution 1 for RendezvousKn.Sym.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T15:37:10.50927+00:00
-- url     : https://prove2.me/submissions/8867d93d-9c44-41dc-80ed-06d4de116165

import Mathlib

namespace RdvCore
open Finset

lemma partition_half {V X : Type*} [Fintype V] [DecidableEq V] [DecidableEq X] (E : Finset X)
    (p : X → V) (n : ℝ) (hn : 0 ≤ n) (hE : 11 / 12 * n ≤ (E.card : ℝ))
    (hdeg : ∀ v, ((E.filter fun e => p e = v).card : ℝ) ≤ 2 / 3 * n) :
    ∃ S : Finset V, n / 4 ≤ ((E.filter fun e => p e ∈ S).card : ℝ) ∧
      n / 4 ≤ ((E.filter fun e => p e ∉ S).card : ℝ) := by
  let d : Finset V → ℝ := fun S => ((E.filter fun e => p e ∈ S).card : ℝ)
  have hcompl : ∀ S, d S + ((E.filter fun e => p e ∉ S).card : ℝ) = E.card := by
    intro S
    have := Finset.card_filter_add_card_filter_not (s := E) (fun e => p e ∈ S)
    simp only [d]; exact_mod_cast this
  have hins : ∀ S v, v ∉ S → d (insert v S) = d S + ((E.filter fun e => p e = v).card : ℝ) := by
    intro S v hv
    simp only [d]
    have : E.filter (fun e => p e ∈ insert v S) =
        E.filter (fun e => p e ∈ S) ∪ E.filter (fun e => p e = v) := by
      ext e; simp only [mem_filter, mem_insert, mem_union]; tauto
    rw [this, card_union_of_disjoint]
    · push_cast; ring
    · rw [Finset.disjoint_filter]
      intro e _ h1 h2; exact hv (h2 ▸ h1)
  have hsing : ∀ v, d {v} = ((E.filter fun e => p e = v).card : ℝ) := by
    intro v; simp only [d, mem_singleton]
  set T := (univ : Finset (Finset V)).filter (fun S => d S ≤ 2 / 3 * n)
  have hT : T.Nonempty := ⟨∅, by simp [T, d]; positivity⟩
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image T d hT
  simp only [T, mem_filter, mem_univ, true_and] at hS hmax
  refine ⟨S, ?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    have hout : 0 < ((E.filter fun e => p e ∉ S).card : ℝ) := by
      have := hcompl S
      have : (0:ℝ) ≤ d S := by positivity
      linarith
    obtain ⟨e, he⟩ : (E.filter fun e => p e ∉ S).Nonempty := by
      rw [← Finset.card_pos]; exact_mod_cast hout
    simp only [mem_filter] at he
    set v := p e
    have hw : (1:ℝ) ≤ ((E.filter fun e => p e = v).card : ℝ) := by
      have : (E.filter fun e' => p e' = v).Nonempty := ⟨e, by simp [he.1, v]⟩
      exact_mod_cast Finset.card_pos.2 this
    by_cases hc : d S + ((E.filter fun e => p e = v).card : ℝ) ≤ 2 / 3 * n
    · have := hmax (insert v S) (by rw [hins S v he.2]; exact hc)
      rw [hins S v he.2] at this
      linarith
    · push Not at hc
      have := hmax {v} (by rw [hsing]; exact hdeg v)
      rw [hsing] at this
      have : (0:ℝ) ≤ d S := by positivity
      linarith
  · have := hcompl S
    linarith

end RdvCore

open Finset

theorem solution {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (n : ℕ) (hA : Fintype.card A = n) (hB : Fintype.card B = n) (E : Finset (A × B))
    (hElo : (11 / 12 : ℝ) * n ≤ (E.card : ℝ)) (hEhi : E.card ≤ n)
    (hdegA : ∀ a : A, ((E.filter fun e => e.1 = a).card : ℝ) ≤ 2 / 3 * n)
    (hdegB : ∀ b : B, ((E.filter fun e => e.2 = b).card : ℝ) ≤ 2 / 3 * n) :
    ∃ E₁ E₂ : Finset (A × B), E₁ ⊆ E ∧ E₂ ⊆ E ∧ Disjoint E₁ E₂ ∧
      (n : ℝ) / 8 ≤ (E₁.card : ℝ) ∧ (n : ℝ) / 8 ≤ (E₂.card : ℝ) ∧
      ∀ e ∈ E₁, ∀ f ∈ E₂, e.1 ≠ f.1 ∧ e.2 ≠ f.2 := by
  obtain ⟨A1, hA1, hA2⟩ := RdvCore.partition_half E Prod.fst (n : ℝ) (by positivity) hElo hdegA
  obtain ⟨B1, hB1, hB2⟩ := RdvCore.partition_half E Prod.snd (n : ℝ) (by positivity) hElo hdegB
  set F11 := E.filter fun e => e.1 ∈ A1 ∧ e.2 ∈ B1
  set F12 := E.filter fun e => e.1 ∈ A1 ∧ e.2 ∉ B1
  set F21 := E.filter fun e => e.1 ∉ A1 ∧ e.2 ∈ B1
  set F22 := E.filter fun e => e.1 ∉ A1 ∧ e.2 ∉ B1
  have split : ∀ (P Q : A × B → Prop) [DecidablePred P] [DecidablePred Q],
      (((E.filter P).filter Q).card : ℝ) + (((E.filter P).filter fun e => ¬ Q e).card : ℝ) =
        ((E.filter P).card : ℝ) := by
    intro P Q _ _
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := E.filter P) Q
  have r1 : (F11.card : ℝ) + F12.card = (E.filter fun e => e.1 ∈ A1).card := by
    have := split (fun e => e.1 ∈ A1) (fun e => e.2 ∈ B1)
    simp only [Finset.filter_filter] at this; exact this
  have r2 : (F21.card : ℝ) + F22.card = (E.filter fun e => e.1 ∉ A1).card := by
    have := split (fun e => e.1 ∉ A1) (fun e => e.2 ∈ B1)
    simp only [Finset.filter_filter] at this; exact this
  have c1 : (F11.card : ℝ) + F21.card = (E.filter fun e => e.2 ∈ B1).card := by
    have := split (fun e => e.2 ∈ B1) (fun e => e.1 ∈ A1)
    simp only [Finset.filter_filter] at this
    have e1 : F11 = E.filter (fun e => e.2 ∈ B1 ∧ e.1 ∈ A1) := by
      simp only [F11]; congr 1; funext e; exact propext and_comm
    have e2 : F21 = E.filter (fun e => e.2 ∈ B1 ∧ ¬ e.1 ∈ A1) := by
      simp only [F21]; congr 1; funext e; exact propext and_comm
    rw [e1, e2]; exact this
  have c2 : (F12.card : ℝ) + F22.card = (E.filter fun e => e.2 ∉ B1).card := by
    have := split (fun e => e.2 ∉ B1) (fun e => e.1 ∈ A1)
    simp only [Finset.filter_filter] at this
    have e1 : F12 = E.filter (fun e => ¬ e.2 ∈ B1 ∧ e.1 ∈ A1) := by
      simp only [F12]; congr 1; funext e; exact propext and_comm
    have e2 : F22 = E.filter (fun e => ¬ e.2 ∈ B1 ∧ ¬ e.1 ∈ A1) := by
      simp only [F22]; congr 1; funext e; exact propext and_comm
    rw [e1, e2]; exact this
  by_cases hdiag : (n : ℝ) / 8 ≤ F11.card ∧ (n : ℝ) / 8 ≤ F22.card
  · refine ⟨F11, F22, filter_subset _ _, filter_subset _ _, ?_, hdiag.1, hdiag.2, ?_⟩
    · rw [Finset.disjoint_filter]; intro e _ h1 h2; exact h2.1 h1.1
    · intro e he f hf
      simp only [F11, F22, mem_filter] at he hf
      exact ⟨fun h => hf.2.1 (h ▸ he.2.1), fun h => hf.2.2 (h ▸ he.2.2)⟩
  by_cases hanti : (n : ℝ) / 8 ≤ F12.card ∧ (n : ℝ) / 8 ≤ F21.card
  · refine ⟨F12, F21, filter_subset _ _, filter_subset _ _, ?_, hanti.1, hanti.2, ?_⟩
    · rw [Finset.disjoint_filter]; intro e _ h1 h2; exact h2.1 h1.1
    · intro e he f hf
      simp only [F12, F21, mem_filter] at he hf
      exact ⟨fun h => hf.2.1 (h ▸ he.2.1), fun h => he.2.2 (h ▸ hf.2.2)⟩
  exfalso
  rw [not_and_or] at hdiag hanti
  push Not at hdiag hanti
  rcases hdiag with h | h <;> rcases hanti with h' | h' <;> linarith
