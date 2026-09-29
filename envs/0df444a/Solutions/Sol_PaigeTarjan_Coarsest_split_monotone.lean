-- Prove2me | solution 1 for PaigeTarjan.Coarsest.split_monotone
-- status  : ACCEPTED   (prove)
-- author  : @37720879
-- created : 2026-09-28T09:06:01.438233+00:00
-- url     : https://prove2.me/submissions/8687360f-c900-4801-abbb-6c9383c7fbff

import Definitions.Def_PaigeTarjan_Coarsest_Basic

open PaigeTarjan.Coarsest

theorem solution {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (P Q : Finset (Finset U)) (S : Finset U)
    (hP : IsPartition P) (hQ : IsPartition Q) (hPQ : Refines P Q) :
    Refines (split E S P) (split E S Q) := by
  intro C hC
  simp only [split] at hC
  obtain ⟨B, hBP, hpiece⟩ := Finset.mem_biUnion.mp hC
  obtain ⟨D, hDQ, hBD⟩ := hPQ B hBP
  have hCne : C.Nonempty := (Finset.mem_filter.mp hpiece).2
  have hcases : C = B ∩ preimage E S ∨ C = B \ preimage E S := by
    have hmem : C ∈ ({B ∩ preimage E S, B \ preimage E S} : Finset (Finset U)) :=
      (Finset.mem_filter.mp hpiece).1
    rcases Finset.mem_insert.mp hmem with hleft | hright
    · exact Or.inl hleft
    · exact Or.inr (Finset.mem_singleton.mp hright)
  rcases hcases with hleft | hright
  · have hCD : C ⊆ D ∩ preimage E S := by
      intro x hx
      rw [hleft] at hx
      exact Finset.mem_inter.mpr ⟨hBD (Finset.mem_inter.mp hx).1,
        (Finset.mem_inter.mp hx).2⟩
    have hDne : (D ∩ preimage E S).Nonempty := by
      obtain ⟨x, hx⟩ := hCne
      exact ⟨x, hCD hx⟩
    refine ⟨D ∩ preimage E S, ?_, hCD⟩
    simp only [split]
    exact Finset.mem_biUnion.mpr ⟨D, hDQ,
      Finset.mem_filter.mpr ⟨by simp, hDne⟩⟩

  · have hCD : C ⊆ D \ preimage E S := by
      intro x hx
      rw [hright] at hx
      exact Finset.mem_sdiff.mpr ⟨hBD (Finset.mem_sdiff.mp hx).1,
        (Finset.mem_sdiff.mp hx).2⟩
    have hDne : (D \ preimage E S).Nonempty := by
      obtain ⟨x, hx⟩ := hCne
      exact ⟨x, hCD hx⟩
    refine ⟨D \ preimage E S, ?_, hCD⟩
    simp only [split]
    exact Finset.mem_biUnion.mpr ⟨D, hDQ,
      Finset.mem_filter.mpr ⟨by simp, hDne⟩⟩
