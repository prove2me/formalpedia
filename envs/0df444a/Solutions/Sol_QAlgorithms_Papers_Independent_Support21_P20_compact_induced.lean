-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P20.compact_induced
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T07:14:46.457369+00:00
-- url     : https://prove2.me/submissions/80454f74-9868-4b81-bb62-4d4199f548af

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20

open QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal

universe u v

theorem solution (X : Type u) (E : Enhanced X)
    (hE : IsCompactEnhancedOn E Set.univ) (m : Set X) (hm : m ∈ E.measurable) :
    IsCompactEnhancedOn E m := by
  obtain ⟨K, hK, hKc, hKa⟩ := hE
  refine ⟨{k | k ∈ K ∧ k ⊆ m}, fun k hk => ⟨hk.2, (hK k hk.1).2⟩, ?_, ?_⟩
  · intro T hT hfin
    rcases T.eq_empty_or_nonempty with hT0 | ⟨t0, ht0⟩
    · subst hT0
      simpa using hfin ∅ Set.finite_empty (Set.empty_subset _)
    · have h := hKc T (fun t ht => (hT ht).1) (fun U hU hUT => by
        obtain ⟨x, hx⟩ := hfin U hU hUT
        exact ⟨x, Set.mem_univ _, hx.2⟩)
      obtain ⟨x, -, hx⟩ := h
      exact ⟨x, (hT ht0).2 (hx t0 ht0), hx⟩
  · intro s hsm hs hsn
    obtain ⟨k, hk, hks, hkn⟩ := hKa s (Set.subset_univ _) hs hsn
    exact ⟨k, ⟨hk, hks.trans hsm⟩, hks, hkn⟩
