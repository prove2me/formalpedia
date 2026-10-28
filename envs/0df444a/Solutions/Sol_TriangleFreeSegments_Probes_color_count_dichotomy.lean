-- Prove2me | solution 1 for TriangleFreeSegments.Probes.color_count_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:54:08.846222+00:00
-- url     : https://prove2.me/submissions/70553ae4-a946-4767-b7cc-c78f4ded5300

import Mathlib
import Definitions.Def_TriangleFreeSegments_Probes_Setting

open TriangleFreeSegments.Probes in
theorem solution {ι α : Type} [Finite ι] (F : ι → Set (ℝ × ℝ)) (φ : ι → α)
    (hφ : ∀ i j, (interGraph F).Adj i j → φ i ≠ φ j) (k : ℕ) (X Y : Set ι) (D : ι)
    (hD : ∀ i ∈ Y, (interGraph F).Adj D i)
    (hX : k ≤ (φ '' X).ncard) (hY : k ≤ (φ '' Y).ncard) :
    (φ '' X ≠ φ '' Y → k + 1 ≤ (φ '' (X ∪ Y)).ncard) ∧
    (φ '' X = φ '' Y → φ D ∉ φ '' Y ∧ k + 1 ≤ (φ '' (insert D X)).ncard) := by
  refine ⟨fun hne => ?_, fun heq => ?_⟩
  · rw [Set.image_union]
    by_cases h1 : φ '' X ∪ φ '' Y = φ '' X
    · have hs : φ '' Y ⊂ φ '' X ∪ φ '' Y := by
        refine Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_union_right, ?_⟩
        intro h2
        exact hne (h1.symm.trans h2.symm)
      have := Set.ncard_lt_ncard hs (Set.toFinite _)
      omega
    · have hs : φ '' X ⊂ φ '' X ∪ φ '' Y :=
        Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_union_left, fun h => h1 h.symm⟩
      have := Set.ncard_lt_ncard hs (Set.toFinite _)
      omega
  · have hD' : φ D ∉ φ '' Y := by
      rintro ⟨i, hi, hiD⟩
      exact hφ D i (hD i hi) hiD.symm
    refine ⟨hD', ?_⟩
    have hDX : φ D ∉ φ '' X := by rw [heq]; exact hD'
    rw [Set.image_insert_eq, Set.ncard_insert_of_notMem hDX (Set.toFinite _)]
    omega
