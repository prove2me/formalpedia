-- Prove2me | solution 1 for Paper.Hypergraph.incidence_elimination_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:18:29.765474+00:00
-- url     : https://prove2.me/submissions/b0f4a2dc-1f9e-45b5-8d77-cd42f3f1003a

import Definitions.Def_Paper_RoundingAveraging
import Definitions.Def_Paper_RoundingDegeneracy

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset MeasureTheory
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) :
    ∃ rank : ℕ ⊕ ℕ → ℕ, Set.InjOn rank (↑H.incidenceVertices : Set (ℕ ⊕ ℕ)) ∧
      ∀ v ∈ H.incidenceVertices,
        (H.incidenceVertices.filter (fun w => H.incidence.Adj v w ∧ rank v < rank w)).card ≤ H.degeneracy := by
  have hdeg : ∀ S ⊆ H.incidenceVertices, S.Nonempty →
      ∃ v ∈ S, (S.filter (H.incidence.Adj v)).card ≤ H.degeneracy := by
    refine csInf_mem (s := {d : ℕ | ∀ S ⊆ H.incidenceVertices, S.Nonempty →
      ∃ v ∈ S, (S.filter (H.incidence.Adj v)).card ≤ d}) ?_
    refine ⟨H.incidenceVertices.card, ?_⟩
    intro S hS hne
    obtain ⟨v, hv⟩ := hne
    exact ⟨v, hv, (card_filter_le _ _).trans (card_le_card hS)⟩
  suffices h : ∀ S ⊆ H.incidenceVertices, ∃ rank : ℕ ⊕ ℕ → ℕ,
      Set.InjOn rank (↑S : Set (ℕ ⊕ ℕ)) ∧ ∀ v ∈ S,
        (S.filter (fun w => H.incidence.Adj v w ∧ rank v < rank w)).card ≤ H.degeneracy from
    h H.incidenceVertices (Subset.refl _)
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hS
    by_cases hne : S.Nonempty
    swap
    · have h0 := Finset.not_nonempty_iff_eq_empty.mp hne
      subst S
      exact ⟨fun _ => 0, by simp, by simp⟩
    obtain ⟨v, hv, hlow⟩ := hdeg S hS hne
    obtain ⟨old, hinj, hlater⟩ := ih (S.erase v) (erase_ssubset hv)
      ((erase_subset _ _).trans hS)
    let rank : ℕ ⊕ ℕ → ℕ := fun w => if w = v then 0 else old w + 1
    refine ⟨rank, ?_, ?_⟩
    · intro a ha b hb heq
      by_cases hav : a = v
      · by_cases hbv : b = v
        · exact hav.trans hbv.symm
        · simp [rank, hav, hbv] at heq
      · by_cases hbv : b = v
        · simp [rank, hav, hbv] at heq
        · apply hinj (mem_erase.mpr ⟨hav, ha⟩) (mem_erase.mpr ⟨hbv, hb⟩)
          simpa [rank, hav, hbv] using heq
    · intro a ha
      by_cases hav : a = v
      · subst a
        apply le_trans (card_le_card ?_) hlow
        intro w hw
        exact mem_filter.mpr ⟨(mem_filter.mp hw).1, (mem_filter.mp hw).2.1⟩
      · apply le_trans _ (hlater a (mem_erase.mpr ⟨hav, ha⟩))
        apply card_le_card
        intro b hb
        obtain ⟨hbS, hab, hrank⟩ := mem_filter.mp hb
        have hbv : b ≠ v := by intro h; simp [rank, h, hav] at hrank
        exact mem_filter.mpr ⟨mem_erase.mpr ⟨hbv, hbS⟩, hab, by simpa [rank, hav, hbv] using hrank⟩
end Paper.Hypergraph
