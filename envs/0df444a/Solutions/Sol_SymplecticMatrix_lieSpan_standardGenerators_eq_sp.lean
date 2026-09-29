-- Prove2me | solution 1 for SymplecticMatrix.lieSpan_standardGenerators_eq_sp
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T15:48:52.566621+00:00
-- url     : https://prove2.me/submissions/6c99c1f9-a174-4f45-bb8d-05bc5e958a16

import Definitions.Def_symplectic_block_generators
import Theorems.Thm_SymplecticMatrix_standardGenerators_mem_sp
import Theorems.Thm_SymplecticMatrix_lie_elemS_elemX
import Theorems.Thm_SymplecticMatrix_span_standardBasisSet_eq_sp

open Matrix SymplecticMatrix

attribute [local instance 100] LieRing.ofAssociativeRing

theorem solution (l : ℕ) (R : Type*) [CommRing R] :
    LieSubalgebra.lieSpan R (Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R)
        (standardGenerators l R)
      = LieAlgebra.Symplectic.sp (Fin l) R := by
  set K := LieSubalgebra.lieSpan R (Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R)
    (standardGenerators l R) with hK
  have hXmem : ∀ p : Fin l × Fin l,
      (elemX p.1 p.2 : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R) ∈ K := fun p =>
    LieSubalgebra.subset_lieSpan (Set.mem_union_left _ (Set.mem_union_left _ ⟨p, rfl⟩))
  have hSmem : ∀ i : Fin l,
      (elemS i i : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R) ∈ K := fun i =>
    LieSubalgebra.subset_lieSpan (Set.mem_union_left _ (Set.mem_union_right _ ⟨i, rfl⟩))
  have hTmem : ∀ p : Fin l × Fin l,
      (elemT p.1 p.2 : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R) ∈ K := fun p =>
    LieSubalgebra.subset_lieSpan (Set.mem_union_right _ ⟨p, rfl⟩)
  refine le_antisymm ?_ ?_
  · -- The generators lie in `sp`, so the Lie span does too.
    rw [hK, LieSubalgebra.lieSpan_le]
    rintro A hA
    rcases hA with (⟨p, rfl⟩ | ⟨i, rfl⟩) | ⟨p, rfl⟩
    · exact (SymplecticMatrix.standardGenerators_mem_sp p.1 p.2).1
    · exact (SymplecticMatrix.standardGenerators_mem_sp i i).2.2
    · exact (SymplecticMatrix.standardGenerators_mem_sp p.1 p.2).2.1
  · -- Conversely the full spanning family lies in `K`, and it spans `sp`.
    intro A hA
    have hsub : standardBasisSet l R ⊆ (K : Set (Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R)) := by
      rintro B ((⟨p, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩)
      · exact hXmem p
      · obtain ⟨a, b⟩ := p
        by_cases h : a = b
        · subst h; exact hSmem a
        · show (elemS a b : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R) ∈
            (K : Set (Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R))
          rw [← SymplecticMatrix.lie_elemS_elemX a b h]
          exact K.lie_mem (hSmem a) (hXmem (a, b))
      · exact hTmem p
    have hspan := Submodule.span_le.mpr hsub
    rw [SymplecticMatrix.span_standardBasisSet_eq_sp] at hspan
    exact hspan hA
