-- Prove2me | solution 1 for ZeroOneExpansion.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:17:07.948524+00:00
-- url     : https://prove2.me/submissions/bbcb1d0b-37ce-4ad6-9791-ee148a38efbe

import Mathlib
import Definitions.Def_ZeroOneExpansion_Pn
import Definitions.Def_ZeroOneExpansion_polyDim

set_option autoImplicit false

open Matrix

namespace ZeroOneExpansion

private lemma zero_mem_Xn (n : ℕ) : (0 : Fin (4 * n) → ℝ) ∈ Xn n := by
  have hzero : (0 : Fin 2 → ℝ) = ![0, 0] := by
    funext j
    fin_cases j <;> rfl
  intro i
  constructor
  · change (0 : Fin 2 → ℝ) ∈ C
    rw [hzero]
    simp [C]
  · change (0 : Fin 2 → ℝ) ∈ D
    rw [hzero]
    simp [D]

private lemma zero_mem_Yn (n : ℕ) : (0 : Fin (4 * n) → ℝ) ∈ Yn n := by
  have hzero : (0 : Fin 2 → ℝ) = ![0, 0] := by
    funext j
    fin_cases j <;> rfl
  intro i
  constructor
  · change (0 : Fin 2 → ℝ) ∈ D
    rw [hzero]
    simp [D]
  · change (0 : Fin 2 → ℝ) ∈ C
    rw [hzero]
    simp [C]

private lemma single_blk_mem_D (n : ℕ) (k : Fin (4 * n)) (b : Fin n ⊕ Fin n) :
    blk n (Pi.single k (1 : ℝ)) b ∈ D := by
  by_cases h0 : k = blockIdx n b 0
  · subst k
    have heq : blk n (Pi.single (blockIdx n b 0) (1 : ℝ)) b = ![1, 0] := by
      funext j
      fin_cases j
      · simp [blk, Pi.single_apply]
      · have h : blockIdx n b 0 ≠ blockIdx n b 1 := by
          cases b <;> simp [blockIdx] <;> omega
        simp [blk, Pi.single_apply, Ne.symm h]
    rw [heq]
    simp [D]
  · by_cases h1 : k = blockIdx n b 1
    · subst k
      have heq : blk n (Pi.single (blockIdx n b 1) (1 : ℝ)) b = ![0, 1] := by
        funext j
        fin_cases j
        · have h : blockIdx n b 0 ≠ blockIdx n b 1 := by
            cases b <;> simp [blockIdx] <;> omega
          simp [blk, Pi.single_apply, h]
        · simp [blk, Pi.single_apply]
      rw [heq]
      simp [D]
    · have heq : blk n (Pi.single k (1 : ℝ)) b = ![0, 0] := by
        funext j
        fin_cases j <;> simp [blk, Pi.single_apply, h0, h1]
      rw [heq]
      simp [D]

private lemma single_mem_Xn (n : ℕ) (k : Fin (4 * n)) :
    Pi.single k (1 : ℝ) ∈ Xn n := by
  have hDC : D ⊆ C := by
    intro x hx
    simp only [D, C, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  intro i
  exact ⟨hDC (single_blk_mem_D n k (Sum.inl i)), single_blk_mem_D n k (Sum.inr i)⟩

private lemma affineSpan_Pn (n : ℕ) : affineSpan ℝ (Pn n) = ⊤ := by
  have hzX : withLast (0 : Fin (4 * n) → ℝ) 0 ∈ Pn n := by
    apply subset_convexHull ℝ
    exact Or.inl ⟨0, zero_mem_Xn n, rfl⟩
  have hzY : withLast (0 : Fin (4 * n) → ℝ) 1 ∈ Pn n := by
    apply subset_convexHull ℝ
    exact Or.inr ⟨0, zero_mem_Yn n, rfl⟩
  rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ _ _ ⟨_, hzX⟩]
  apply top_unique
  rw [← (Pi.basisFun ℝ (Fin (4 * n + 1))).span_eq]
  apply Submodule.span_le.2
  intro v hv
  obtain ⟨i, rfl⟩ := Set.mem_range.1 hv
  simp only [Pi.basisFun_apply]
  refine Fin.lastCases ?_ (fun k => ?_) i
  · have heq : Pi.single (Fin.last (4 * n)) (1 : ℝ) =
        withLast (0 : Fin (4 * n) → ℝ) 1 -ᵥ withLast (0 : Fin (4 * n) → ℝ) 0 := by
      ext j
      refine Fin.lastCases ?_ (fun k => ?_) j
      · simp [withLast, Pi.single_apply]
      · simp [withLast, Pi.single_apply]
    rw [heq]
    exact vsub_mem_vectorSpan ℝ hzY hzX
  · have hp : withLast (Pi.single k (1 : ℝ)) 0 ∈ Pn n := by
      apply subset_convexHull ℝ
      exact Or.inl ⟨Pi.single k 1, single_mem_Xn n k, rfl⟩
    have heq : Pi.single k.castSucc (1 : ℝ) =
        withLast (Pi.single k (1 : ℝ)) 0 -ᵥ withLast (0 : Fin (4 * n) → ℝ) 0 := by
      ext j
      refine Fin.lastCases ?_ (fun l => ?_) j
      · simp [withLast, Pi.single_apply]
      · simp [withLast, Pi.single_apply]
    rw [heq]
    exact vsub_mem_vectorSpan ℝ hp hzX

end ZeroOneExpansion

open ZeroOneExpansion

theorem solution (n : ℕ) (hn : 1 ≤ n) : polyDim (Pn n) = 4 * n + 1 := by
  rw [polyDim, affineSpan_Pn, AffineSubspace.direction_top, finrank_top]
  exact Module.finrank_fin_fun ℝ
