-- Prove2me | solution 1 for SymplecticMatrix.finrank_sp
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T17:11:13.47496+00:00
-- url     : https://prove2.me/submissions/61a48e8b-5705-4659-b92c-f930c72eeb48

import Definitions.Def_symplectic_block_generators
import Theorems.Thm_SymplecticMatrix_standardFamily_linearIndependent
import Theorems.Thm_SymplecticMatrix_span_standardBasisSet_eq_sp

open Matrix SymplecticMatrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {l : ℕ} {R : Type*} [CommRing R]

abbrev SIdx (l : ℕ) := (Fin l × Fin l) ⊕ {p : Fin l × Fin l // p.1 ≤ p.2} ⊕
  {p : Fin l × Fin l // p.1 ≤ p.2}

noncomputable def sfam (l : ℕ) (R : Type*) [CommRing R] :
    SIdx l → Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R :=
  Sum.elim (fun p => elemX p.1 p.2)
    (Sum.elim (fun p => elemT p.1.1 p.1.2) (fun p => elemS p.1.1 p.1.2))

private lemma symmMatrix_comm (i j : Fin l) :
    (symmMatrix i j : Matrix (Fin l) (Fin l) R) = symmMatrix j i := by
  unfold symmMatrix
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h), add_comm]

private lemma span_range_sfam (l : ℕ) (R : Type*) [CommRing R] :
    Submodule.span R (Set.range (sfam l R))
      = (LieAlgebra.Symplectic.sp (Fin l) R).toSubmodule := by
  rw [← SymplecticMatrix.span_standardBasisSet_eq_sp l R]
  refine le_antisymm (Submodule.span_mono ?_) ?_
  · rintro A ⟨x, rfl⟩
    rcases x with p | (q | q)
    · exact Set.mem_union_left _ (Set.mem_union_left _ ⟨p, rfl⟩)
    · exact Set.mem_union_right _ ⟨q.1, rfl⟩
    · exact Set.mem_union_left _ (Set.mem_union_right _ ⟨q.1, rfl⟩)
  · rw [Submodule.span_le]
    rintro A ((⟨p, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩)
    · exact Submodule.subset_span ⟨Sum.inl p, rfl⟩
    · show (elemS p.1 p.2 : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R) ∈ _
      rcases le_total p.1 p.2 with h | h
      · exact Submodule.subset_span ⟨Sum.inr (Sum.inr ⟨p, h⟩), rfl⟩
      · rw [elemS, symmMatrix_comm]
        exact Submodule.subset_span ⟨Sum.inr (Sum.inr ⟨(p.2, p.1), h⟩), rfl⟩
    · show (elemT p.1 p.2 : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R) ∈ _
      rcases le_total p.1 p.2 with h | h
      · exact Submodule.subset_span ⟨Sum.inr (Sum.inl ⟨p, h⟩), rfl⟩
      · rw [elemT, symmMatrix_comm]
        exact Submodule.subset_span ⟨Sum.inr (Sum.inl ⟨(p.2, p.1), h⟩), rfl⟩

private lemma two_choose (n : ℕ) : 2 * Nat.choose (n + 1) 2 = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Nat.choose_succ_succ (m + 1) 1, Nat.choose_one_right]
      norm_num
      have hm : (m + 1) * (m + 1 + 1) = 2 * (m + 1) + m * (m + 1) := by ring
      omega

private lemma card_SIdx (l : ℕ) : Fintype.card (SIdx l) = l * (2 * l + 1) := by
  have hpair : Fintype.card {p : Fin l × Fin l // p.1 ≤ p.2} = Nat.choose (l + 1) 2 := by
    rw [← Fintype.card_congr (Sym2.sortEquiv (α := Fin l)), Sym2.card, Fintype.card_fin]
  have key := two_choose l
  have hexp : l * (l + 1) = l * l + l := by ring
  have hgoal : l * (2 * l + 1) = l * l + (l * l + l) := by ring
  simp only [SIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, hpair]
  omega

theorem solution (l : ℕ) (R : Type*) [Field R] :
    Module.finrank R (LieAlgebra.Symplectic.sp (Fin l) R) = l * (2 * l + 1) := by
  classical
  have hmem : ∀ x : SIdx l, sfam l R x ∈ LieAlgebra.Symplectic.sp (Fin l) R := fun x => by
    have h := span_range_sfam l R
    have : sfam l R x ∈ Submodule.span R (Set.range (sfam l R)) :=
      Submodule.subset_span ⟨x, rfl⟩
    rwa [h] at this
  set v : SIdx l → (LieAlgebra.Symplectic.sp (Fin l) R) := fun x => ⟨sfam l R x, hmem x⟩ with hv
  have hLI : LinearIndependent R v := by
    refine LinearIndependent.of_comp
      (LieAlgebra.Symplectic.sp (Fin l) R).toSubmodule.subtype ?_
    exact SymplecticMatrix.standardFamily_linearIndependent l R
  have hspan : ⊤ ≤ Submodule.span R (Set.range v) := by
    have hmap : Submodule.map (LieAlgebra.Symplectic.sp (Fin l) R).toSubmodule.subtype
        (Submodule.span R (Set.range v)) = Submodule.span R (Set.range (sfam l R)) := by
      rw [← Submodule.span_image, ← Set.range_comp]
      rfl
    have h1 : Submodule.map (LieAlgebra.Symplectic.sp (Fin l) R).toSubmodule.subtype
        (Submodule.span R (Set.range v))
        = Submodule.map (LieAlgebra.Symplectic.sp (Fin l) R).toSubmodule.subtype ⊤ := by
      rw [hmap, span_range_sfam, Submodule.map_subtype_top]
    have h2 := Submodule.map_injective_of_injective
      (Submodule.injective_subtype _) h1
    exact le_of_eq h2.symm
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hLI hspan), card_SIdx]
