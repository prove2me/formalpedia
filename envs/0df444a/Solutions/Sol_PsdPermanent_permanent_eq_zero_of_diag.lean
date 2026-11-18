-- Prove2me | solution 1 for PsdPermanent.permanent_eq_zero_of_diag
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:29:57.969497+00:00
-- url     : https://prove2.me/submissions/128f1da6-da4e-4e47-86be-04d90840e298

import Mathlib
open Matrix
open scoped ComplexOrder
namespace PsdPermanent

theorem permanent_eq_zero_of_diag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef) (i : Fin n)
    (hi : A i i = 0) :
    (∀ (d : ℕ) (V : Matrix (Fin n) (Fin d) ℂ), A = V * Vᴴ → V i = 0) ∧
      (∀ j, Complex.normSq (A i j) ≤ (A i i).re * (A j j).re) ∧
      (∀ j, A i j = 0 ∧ A j i = 0) ∧ A.permanent = 0 := by
  have hcol : A *ᵥ Pi.single i 1 = 0 := by
    rw [← hA.dotProduct_mulVec_zero_iff]
    simp [hi]
  have hji : ∀ j, A j i = 0 := by
    intro j
    have := congrFun hcol j
    simpa [mulVec, dotProduct, Pi.single_apply] using this
  have hij : ∀ j, A i j = 0 := by
    intro j
    have h := hA.isHermitian.apply i j
    rw [hji j] at h
    simpa using h.symm
  refine ⟨?_, ?_, fun j => ⟨hij j, hji j⟩, ?_⟩
  · intro d V hV
    have h : (V * Vᴴ) i i = 0 := by rw [← hV]; exact hi
    have h2 : star (V i) ⬝ᵥ V i = 0 := by
      rw [dotProduct_comm]
      simpa [mul_apply, dotProduct] using h
    exact dotProduct_star_self_eq_zero.mp h2
  · intro j
    rw [hij j, hi]; simp
  · unfold Matrix.permanent
    apply Finset.sum_eq_zero
    intro σ _
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hji (σ i))

end PsdPermanent

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef) (i : Fin n)
    (hi : A i i = 0) :
    (∀ (d : ℕ) (V : Matrix (Fin n) (Fin d) ℂ), A = V * Vᴴ → V i = 0) ∧
      (∀ j, Complex.normSq (A i j) ≤ (A i i).re * (A j j).re) ∧
      (∀ j, A i j = 0 ∧ A j i = 0) ∧ A.permanent = 0 :=
  PsdPermanent.permanent_eq_zero_of_diag A hA i hi
