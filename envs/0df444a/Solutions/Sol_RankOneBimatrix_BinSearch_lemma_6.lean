-- Prove2me | solution 1 for RankOneBimatrix.BinSearch.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:56:02.112999+00:00
-- url     : https://prove2.me/submissions/dbf8508b-c275-4a42-bcf0-47e54b2912e1

import Definitions.Def_RankOneBimatrix_BinSearch_Setting

open Matrix

open RankOneBimatrix.BinSearch in
theorem solution {m n : ℕ} (A C : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) (a : Fin m → ℝ) (b : Fin n → ℝ)
    (lam : ℝ) (hx : x ∈ Mixed m) (hy : y ∈ Mixed n) :
    (x ⬝ᵥ a = lam →
      (IsNE A (C + vecMulVec a b) x y ↔
        IsNE A (C + onesLam lam b) x y ∧ x ⬝ᵥ a = lam)) ∧
    (IsNE A (C + onesLam lam b) x y ∧ x ⬝ᵥ a = lam ↔
      IsNE (A - onesLam lam b) (C + onesLam lam b) x y ∧
        x ⬝ᵥ a = lam) := by
  have hR : ∀ (u x' : Fin m → ℝ) (v y' : Fin n → ℝ),
      x' ⬝ᵥ (vecMulVec u v *ᵥ y') = (x' ⬝ᵥ u) * (v ⬝ᵥ y') := by
    intro u x' v y'
    rw [vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, smul_eq_mul, mul_comm]
  have hO : ∀ x' ∈ Mixed m, ∀ y' : Fin n → ℝ,
      x' ⬝ᵥ (onesLam lam b *ᵥ y') = lam * (b ⬝ᵥ y') := by
    intro x' hx' y'
    unfold onesLam
    rw [hR, smul_dotProduct, smul_eq_mul]
    have : x' ⬝ᵥ (fun _ => (1 : ℝ)) = 1 := by
      simp only [dotProduct, mul_one]
      exact hx'.2
    rw [this, one_mul]
  constructor
  · intro ha
    constructor
    · rintro ⟨hx1, hy1, hrow, hcol⟩
      refine ⟨⟨hx1, hy1, hrow, ?_⟩, ha⟩
      intro y' hy'
      have := hcol y' hy'
      simp only [add_mulVec, dotProduct_add] at this ⊢
      rw [hR, hR, ha] at this
      rw [hO x hx, hO x hx]
      exact this
    · rintro ⟨⟨hx1, hy1, hrow, hcol⟩, -⟩
      refine ⟨hx1, hy1, hrow, ?_⟩
      intro y' hy'
      have := hcol y' hy'
      simp only [add_mulVec, dotProduct_add] at this ⊢
      rw [hO x hx, hO x hx] at this
      rw [hR, hR, ha]
      exact this
  · constructor
    · rintro ⟨⟨hx1, hy1, hrow, hcol⟩, ha⟩
      refine ⟨⟨hx1, hy1, ?_, hcol⟩, ha⟩
      intro x' hx'
      rw [sub_mulVec, dotProduct_sub, dotProduct_sub, hO x' hx', hO x hx]
      linarith [hrow x' hx']
    · rintro ⟨⟨hx1, hy1, hrow, hcol⟩, ha⟩
      refine ⟨⟨hx1, hy1, ?_, hcol⟩, ha⟩
      intro x' hx'
      have := hrow x' hx'
      rw [sub_mulVec, dotProduct_sub, dotProduct_sub, hO x' hx', hO x hx] at this
      linarith
