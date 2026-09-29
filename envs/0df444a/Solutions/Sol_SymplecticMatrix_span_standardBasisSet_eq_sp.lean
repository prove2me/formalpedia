-- Prove2me | solution 1 for SymplecticMatrix.span_standardBasisSet_eq_sp
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T16:56:04.920993+00:00
-- url     : https://prove2.me/submissions/aa94044e-39cb-460b-9773-61fb93cfe673

import Definitions.Def_symplectic_block_generators
import Theorems.Thm_SymplecticMatrix_mem_sp_iff_blocks
import Theorems.Thm_SymplecticMatrix_standardGenerators_mem_sp

open Matrix SymplecticMatrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {l : ℕ} {R : Type*} [CommRing R]

private lemma symmMatrix_apply (i j x y : Fin l) :
    (symmMatrix i j : Matrix (Fin l) (Fin l) R) x y
      = (if i = x ∧ j = y then 1 else 0)
        + (if i ≠ j ∧ j = x ∧ i = y then 1 else 0) := by
  by_cases h : i = j
  · subst h; simp [symmMatrix, Matrix.single]
  · simp [symmMatrix, h, Matrix.single]

private lemma symm_sum (b : Matrix (Fin l) (Fin l) R) (hb : b.transpose = b) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin l × Fin l => p.1 ≤ p.2),
        b p.1 p.2 • (symmMatrix p.1 p.2 : Matrix (Fin l) (Fin l) R) = b := by
  have hsym : ∀ u v : Fin l, b v u = b u v := fun u v => congrFun (congrFun hb u) v
  ext x y
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, symmMatrix_apply, mul_add, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_add_distrib]
  have e1 : ∀ p : Fin l × Fin l,
      (if p.1 = x ∧ p.2 = y then b p.1 p.2 else 0)
        = (if p = (x, y) then b x y else 0) := by
    intro p
    by_cases hp : p = (x, y)
    · subst hp; simp
    · rw [if_neg hp, if_neg]
      rintro ⟨h1, h2⟩
      exact hp (Prod.ext h1 h2)
  have e2 : ∀ p : Fin l × Fin l,
      (if p.1 ≠ p.2 ∧ p.2 = x ∧ p.1 = y then b p.1 p.2 else 0)
        = (if p = (y, x) then (if y ≠ x then b x y else 0) else 0) := by
    intro p
    by_cases hp : p = (y, x)
    · subst hp; simp [hsym]
    · rw [if_neg hp, if_neg]
      rintro ⟨-, h1, h2⟩
      exact hp (Prod.ext h2 h1)
  simp only [e1, e2, Finset.sum_ite_eq' (Finset.univ.filter (fun p : Fin l × Fin l => p.1 ≤ p.2))]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases lt_trichotomy x y with h | h | h
  · simp [le_of_lt h, not_le.mpr h, h.ne']
  · subst h; simp
  · simp [not_le.mpr h, le_of_lt h, h.ne, hsym]

private lemma sum_elemX (a : Matrix (Fin l) (Fin l) R) :
    (∑ i : Fin l, ∑ j : Fin l,
        a i j • (elemX i j : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R))
      = Matrix.fromBlocks a 0 0 (-a.transpose) := by
  ext p q
  rcases p with p | p <;> rcases q with q | q <;>
    simp [elemX, Matrix.sum_apply, Matrix.single, Matrix.transpose_apply, ite_and]

private lemma sum_elemT (b : Matrix (Fin l) (Fin l) R) (hb : b.transpose = b) :
    (∑ p ∈ Finset.univ.filter (fun p : Fin l × Fin l => p.1 ≤ p.2),
        b p.1 p.2 • (elemT p.1 p.2 : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R))
      = Matrix.fromBlocks 0 b 0 0 := by
  ext p q
  have key := symm_sum b hb
  rcases p with p | p <;> rcases q with q | q <;>
    simp [elemT, Matrix.sum_apply]
  have := congrFun (congrFun key p) q
  simpa [Matrix.sum_apply] using this

private lemma sum_elemS (c : Matrix (Fin l) (Fin l) R) (hc : c.transpose = c) :
    (∑ p ∈ Finset.univ.filter (fun p : Fin l × Fin l => p.1 ≤ p.2),
        c p.1 p.2 • (elemS p.1 p.2 : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R))
      = Matrix.fromBlocks 0 0 c 0 := by
  ext p q
  have key := symm_sum c hc
  rcases p with p | p <;> rcases q with q | q <;>
    simp [elemS, Matrix.sum_apply]
  have := congrFun (congrFun key p) q
  simpa [Matrix.sum_apply] using this

theorem solution (l : ℕ) (R : Type*) [CommRing R] :
    Submodule.span R (standardBasisSet l R)
      = (LieAlgebra.Symplectic.sp (Fin l) R).toSubmodule := by
  classical
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro A ((⟨p, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩)
    · exact (SymplecticMatrix.standardGenerators_mem_sp p.1 p.2).1
    · exact (SymplecticMatrix.standardGenerators_mem_sp p.1 p.2).2.2
    · exact (SymplecticMatrix.standardGenerators_mem_sp p.1 p.2).2.1
  · intro A hA
    rw [← Matrix.fromBlocks_toBlocks A] at hA ⊢
    obtain ⟨hd, hb, hc⟩ :=
      (SymplecticMatrix.mem_sp_iff_blocks A.toBlocks₁₁ A.toBlocks₁₂ A.toBlocks₂₁
        A.toBlocks₂₂).mp hA
    rw [hd, show Matrix.fromBlocks A.toBlocks₁₁ A.toBlocks₁₂ A.toBlocks₂₁
          (-A.toBlocks₁₁.transpose)
        = Matrix.fromBlocks A.toBlocks₁₁ 0 0 (-A.toBlocks₁₁.transpose)
          + Matrix.fromBlocks 0 A.toBlocks₁₂ 0 0
          + Matrix.fromBlocks 0 0 A.toBlocks₂₁ 0 by
      rw [Matrix.fromBlocks_add, Matrix.fromBlocks_add]; simp]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · rw [← sum_elemX]
      exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span
          (Set.mem_union_left _ (Set.mem_union_left _ ⟨(i, j), rfl⟩)))
    · rw [← sum_elemT _ hb]
      exact Submodule.sum_mem _ fun p _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span
          (Set.mem_union_right _ ⟨p, rfl⟩))
    · rw [← sum_elemS _ hc]
      exact Submodule.sum_mem _ fun p _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span
          (Set.mem_union_left _ (Set.mem_union_right _ ⟨p, rfl⟩)))
