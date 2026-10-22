-- Prove2me | solution 1 for WeingartenCalc.Fundamental.projection_factorization
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T21:17:19.712335+00:00
-- url     : https://prove2.me/submissions/d41fab19-8882-4f7f-85ca-dde49aaf4c63

import Mathlib
import Definitions.Def_WeingartenCalc_Fundamental_TensorPower

open MeasureTheory Matrix
open scoped ComplexOrder
open WeingartenCalc.Fundamental

theorem solution
    {n : Type*} [Fintype n] [DecidableEq n] {m : ℕ} (a : Fin m → (n → ℂ))
    (ha : LinearIndependent ℂ a) (P : Matrix n n ℂ) (hPh : Pᴴ = P) (hPP : P * P = P)
    (hrange : LinearMap.range P.mulVecLin = Submodule.span ℂ (Set.range a)) :
    P = coordMatrix a * ((coordMatrix a)ᴴ * coordMatrix a)⁻¹ * (coordMatrix a)ᴴ := by
  set A := coordMatrix a with hA
  have hAv : ∀ c : Fin m → ℂ, A *ᵥ c = ∑ x, c x • a x := by
    intro c; ext i
    simp [hA, coordMatrix, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  set G := Aᴴ * A with hG
  have hGinj : Function.Injective G.mulVec := by
    intro c d h
    have h0 : (Aᴴ * A) *ᵥ (c - d) = 0 := by
      rw [Matrix.mulVec_sub, sub_eq_zero]; exact h
    rw [conjTranspose_mul_self_mulVec_eq_zero, hAv] at h0
    have := Fintype.linearIndependent_iff.mp ha _ h0
    funext x; exact sub_eq_zero.mp (this x)
  have hGu : IsUnit G := Matrix.mulVec_injective_iff_isUnit.mp hGinj
  have hGdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hGu
  have hGinvG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hGdet
  set Q := A * G⁻¹ * Aᴴ with hQ
  have hQA : Q * A = A := by
    rw [hQ, Matrix.mul_assoc, Matrix.mul_assoc, ← hG, hGinvG, Matrix.mul_one]
  -- columns of A are fixed by P
  have hPA : P * A = A := by
    ext i x
    have hmem : a x ∈ LinearMap.range P.mulVecLin := by
      rw [hrange]; exact Submodule.subset_span ⟨x, rfl⟩
    obtain ⟨w, hw⟩ := hmem
    simp only [Matrix.mulVecLin_apply] at hw
    have : P *ᵥ a x = a x := by rw [← hw, Matrix.mulVec_mulVec, hPP]
    have := congrFun this i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, hA, coordMatrix] using this
  -- P = A * C
  have hcol : ∀ j : n, ∃ c : Fin m → ℂ, ∑ x, c x • a x = P *ᵥ Pi.single j 1 := by
    intro j
    have hmem : P *ᵥ Pi.single j 1 ∈ Submodule.span ℂ (Set.range a) := by
      rw [← hrange]; exact ⟨_, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  choose c hc using hcol
  have hPAC : P = A * Matrix.of (fun x j => c j x) := by
    ext i j
    have := congrFun (hc j) i
    rw [Matrix.mulVec_single_one] at this
    simp only [Matrix.col_apply] at this
    rw [← this]
    simp [Matrix.mul_apply, hA, coordMatrix, Finset.sum_apply, mul_comm]
  have hQP : Q * P = P := by rw [hPAC, ← Matrix.mul_assoc, hQA]
  have hPQ : P * Q = Q := by rw [hQ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPA]
  have hQh : Qᴴ = Q := by
    rw [hQ, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      conjTranspose_nonsing_inv, hG, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  calc P = Pᴴ := hPh.symm
    _ = (Q * P)ᴴ := by rw [hQP]
    _ = P * Q := by rw [conjTranspose_mul, hPh, hQh]
    _ = Q := hPQ
