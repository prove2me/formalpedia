-- Prove2me | solution 1 for SpanForestStream.Unrestricted.eq_3_1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T06:38:27.55194+00:00
-- url     : https://prove2.me/submissions/1912cde6-ef41-43b5-b0bf-7d1b2182d256

import Mathlib

open Matrix

theorem solution {v s : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (H : Matrix (Fin s) (Fin v) (ZMod 2)) (C : Finset (Fin v)) :
    let X : Matrix (Fin v) (Fin v) (ZMod 2) := G.adjMatrix (ZMod 2)
    let IC : Matrix (Fin v) (Fin v) (ZMod 2) := Matrix.diagonal fun u => if u ∈ C then 1 else 0
    let XC : Matrix (Fin v) (Fin v) (ZMod 2) :=
      fun a b => if G.Adj a b ∧ (a ∈ C ↔ b ∉ C) then 1 else 0
    let h : Fin v → Fin s → ZMod 2 := fun u => H.mulVec (Pi.single u 1)
    let y : Fin v → Fin s → ZMod 2 := fun u => (H * X).mulVec (Pi.single u 1)
    XC = IC * X + X * IC ∧
      ∑ u ∈ C, (Matrix.vecMulVec (h u) (y u) + Matrix.vecMulVec (y u) (h u)) =
        H * (IC * X + X * IC) * H.transpose ∧
      H * (IC * X + X * IC) * H.transpose = H * XC * H.transpose := by
  dsimp only
  set X : Matrix (Fin v) (Fin v) (ZMod 2) := G.adjMatrix (ZMod 2) with hX
  set IC : Matrix (Fin v) (Fin v) (ZMod 2) := Matrix.diagonal (fun u => if u ∈ C then 1 else 0) with hIC
  set XC : Matrix (Fin v) (Fin v) (ZMod 2) :=
    fun a b => if G.Adj a b ∧ (a ∈ C ↔ b ∉ C) then 1 else 0 with hXC
  have h1 : XC = IC * X + X * IC := by
    rw [hXC]
    ext a b
    rw [hIC, hX, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, SimpleGraph.adjMatrix_apply]
        by_cases ha : a ∈ C <;> by_cases hb : b ∈ C <;> by_cases hadj : G.Adj a b <;>
          simp_all <;> decide
      · intro k _ hk
        rw [Matrix.diagonal_apply_ne _ hk, mul_zero]
      · intro h; exact absurd (Finset.mem_univ b) h
    · intro k _ hk
      rw [Matrix.diagonal_apply_ne _ ?_, zero_mul]
      exact fun h => hk h.symm
    · intro h; exact absurd (Finset.mem_univ a) h
  set E : Fin v → Matrix (Fin v) (Fin v) (ZMod 2) :=
    fun u => Matrix.vecMulVec (Pi.single u 1) (Pi.single u 1) with hE
  have hXs : Xᵀ = X := by
    rw [hX]
    ext a b
    rw [Matrix.transpose_apply, SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply]
    by_cases hab : G.Adj a b
    · have hba : G.Adj b a := (G.adj_comm a b).mp hab
      rw [if_pos hba, if_pos hab]
    · have hba : ¬ G.Adj b a := fun h => hab ((G.adj_comm b a).mp h)
      rw [if_neg hba, if_neg hab]
  have hEsum : ∑ u ∈ C, E u = IC := by
    rw [hIC]
    ext a b
    rw [Matrix.sum_apply, Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl]
      have hterm : ∀ u, E u a a = if a = u then (1 : ZMod 2) else 0 := by
        intro u
        simp only [hE, Matrix.vecMulVec_apply, Pi.single_apply]
        by_cases hau : a = u
        · rw [if_pos hau]; simp
        · rw [if_neg hau]; simp
      simp only [hterm]
      rw [Finset.sum_ite_eq]
    · rw [if_neg hab]
      apply Finset.sum_eq_zero
      intro u _
      simp only [hE, Matrix.vecMulVec_apply, Pi.single_apply]
      by_cases hau : a = u
      · have hbu : b ≠ u := by intro hbu; exact hab (hau.trans hbu.symm)
        rw [if_pos hau, if_neg hbu]; simp
      · rw [if_neg hau]; simp
  have keyA : ∀ (A : Matrix (Fin s) (Fin v) (ZMod 2)) (u : Fin v),
      Matrix.vecMulVec (Pi.single u 1) (A *ᵥ Pi.single u 1) = E u * Aᵀ := by
    intro A u
    rw [hE]
    simp only
    rw [Matrix.vecMulVec_mul]
    congr 1
    rw [← Matrix.mulVec_transpose (A := Aᵀ), Matrix.transpose_transpose]
  have e1 : ∀ u : Fin v,
      Matrix.vecMulVec (H *ᵥ Pi.single u 1) ((H * X) *ᵥ Pi.single u 1) = H * E u * Xᵀ * Hᵀ := by
    intro u
    rw [← Matrix.mul_vecMulVec (M := H) (x := Pi.single u 1), keyA (H * X) u, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  have e2 : ∀ u : Fin v,
      Matrix.vecMulVec ((H * X) *ᵥ Pi.single u 1) (H *ᵥ Pi.single u 1) = H * X * E u * Hᵀ := by
    intro u
    rw [← Matrix.mul_vecMulVec (M := H * X) (x := Pi.single u 1), keyA H u]
    simp only [Matrix.mul_assoc]
  have hfac1 : ∑ u ∈ C, H * E u * Xᵀ * Hᵀ = H * (∑ u ∈ C, E u) * Xᵀ * Hᵀ := by
    rw [← Matrix.sum_mul, ← Matrix.sum_mul, ← Matrix.mul_sum]
  have hfac2 : ∑ u ∈ C, H * X * E u * Hᵀ = H * X * (∑ u ∈ C, E u) * Hᵀ := by
    rw [← Matrix.sum_mul, ← Matrix.mul_sum]
  have h2 : ∑ u ∈ C, (Matrix.vecMulVec (H *ᵥ Pi.single u 1) ((H * X) *ᵥ Pi.single u 1) +
        Matrix.vecMulVec ((H * X) *ᵥ Pi.single u 1) (H *ᵥ Pi.single u 1)) =
      H * (IC * X + X * IC) * Hᵀ := by
    calc ∑ u ∈ C, (Matrix.vecMulVec (H *ᵥ Pi.single u 1) ((H * X) *ᵥ Pi.single u 1) +
          Matrix.vecMulVec ((H * X) *ᵥ Pi.single u 1) (H *ᵥ Pi.single u 1))
        = ∑ u ∈ C, (H * E u * Xᵀ * Hᵀ + H * X * E u * Hᵀ) := by
          apply Finset.sum_congr rfl
          intro u _
          rw [e1 u, e2 u]
      _ = (∑ u ∈ C, H * E u * Xᵀ * Hᵀ) + ∑ u ∈ C, H * X * E u * Hᵀ := Finset.sum_add_distrib
      _ = H * (∑ u ∈ C, E u) * Xᵀ * Hᵀ + H * X * (∑ u ∈ C, E u) * Hᵀ := by rw [hfac1, hfac2]
      _ = H * (IC * X + X * IC) * Hᵀ := by
          rw [hEsum, hXs, Matrix.mul_add, Matrix.add_mul]
          simp only [Matrix.mul_assoc]
  have h3 : H * (IC * X + X * IC) * Hᵀ = H * XC * Hᵀ := by
    rw [h1]
  exact ⟨h1, h2, h3⟩
