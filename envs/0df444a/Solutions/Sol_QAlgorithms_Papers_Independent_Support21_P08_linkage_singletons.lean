-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P08.linkage_singletons
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T07:47:54.030905+00:00
-- url     : https://prove2.me/submissions/90cee3b8-4b73-4ff1-aa3d-8e667c5fefa6

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08
noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support21.P08

open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)

open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section AppendixDefinitions

variable {R : Type*} [CommRing R]

theorem g67d_mem_class [IsLocalRing R] {d n : ℕ} (S : TriangularSystem R d n) (i j : Fin d) :
    j ∈ linkageClass S i ↔ linked S i j := by
  simp [linkageClass]

theorem g67d_class_eq [IsLocalRing R] {d n : ℕ} (S : TriangularSystem R d n) (i j : Fin d)
    (h : linked S i j) : linkageClass S i = linkageClass S j := by
  ext x
  rw [g67d_mem_class, g67d_mem_class]
  constructor
  · intro hx k; rw [← h k, hx k]
  · intro hx k; rw [h k, hx k]

theorem solution [IsDomain R] [IsLocalRing R] {d n : ℕ}
    (S : TriangularSystem R d n) :
    (∀ J ∈ linkagePartition S, J.Nonempty) ∧
    (∀ J ∈ linkagePartition S, ∀ U ∈ linkagePartition S, J ≠ U → Disjoint J U) ∧
    (∀ i : Fin d, ∃ J ∈ linkagePartition S, i ∈ J) ∧
    (UnitSeparating S ↔ ∀ i : Fin d, linkageClass S i = {i}) := by
  have hrefl : ∀ i, linked S i i := fun i k => rfl
  have hmem : ∀ J ∈ linkagePartition S, ∃ i, J = linkageClass S i := by
    intro J hJ
    simp only [linkagePartition, Finset.mem_image, Finset.mem_univ, true_and] at hJ
    obtain ⟨i, rfl⟩ := hJ
    exact ⟨i, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro J hJ
    obtain ⟨i, rfl⟩ := hmem J hJ
    exact ⟨i, (g67d_mem_class S i i).2 (hrefl i)⟩
  · intro J hJ U hU hne
    obtain ⟨i, rfl⟩ := hmem J hJ
    obtain ⟨j, rfl⟩ := hmem U hU
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [g67d_mem_class] at hx hx'
    apply hne
    rw [g67d_class_eq S i x hx, g67d_class_eq S j x hx']
  · intro i
    exact ⟨linkageClass S i, by simp [linkagePartition], (g67d_mem_class S i i).2 (hrefl i)⟩
  · have key : ∀ i j : Fin d, (∃ k, IsUnit (triangularDiagonalEntry S k i -
        triangularDiagonalEntry S k j)) ↔ ¬ linked S i j := by
      intro i j
      simp only [linked, not_forall]
      refine exists_congr (fun k => ?_)
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub, sub_ne_zero]
    constructor
    · intro h i
      ext j
      rw [g67d_mem_class, Finset.mem_singleton]
      constructor
      · intro hl
        by_contra hji
        exact (key i j).1 (h i j (Ne.symm hji)) hl
      · rintro rfl; exact hrefl j
    · intro h i j hij
      rw [key]
      intro hl
      have := (g67d_mem_class S i j).2 hl
      rw [h i, Finset.mem_singleton] at this
      exact hij this.symm

end AppendixDefinitions

end
