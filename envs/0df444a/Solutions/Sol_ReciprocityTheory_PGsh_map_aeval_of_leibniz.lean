-- Prove2me | solution 1 for ReciprocityTheory.PGsh.map_aeval_of_leibniz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:37:33.952596+00:00
-- url     : https://prove2.me/submissions/77cd040f-e24a-4efd-9208-e612478ae899

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
namespace ReciprocityTheory.PGsh
theorem _root_.solution {d : ℕ} (D : A →ₗ[R] A) (hD : ∀ f g, D (f * g) = f * D g + g * D f)
    (x : Fin d → A) (P : MvPolynomial (Fin d) R) :
    D (aeval x P) = ∑ j, aeval x (pderiv j P) * D (x j) := by
  classical
  have h1 : D 1 = 0 := by
    have h := hD 1 1
    simp only [one_mul] at h
    linear_combination -h
  induction P using MvPolynomial.induction_on with
  | C a => simp [Algebra.algebraMap_eq_smul_one, h1]
  | add P Q hP hQ => simp only [map_add, hP, hQ, add_mul, Finset.sum_add_distrib]
  | mul_X P n hP =>
    have hs : ∑ j, aeval x (pderiv j (P * X n)) * D (x j) =
        x n * ∑ j, aeval x (pderiv j P) * D (x j) + aeval x P * D (x n) := by
      have : ∀ j, aeval x (pderiv j (P * X n)) * D (x j) =
          x n * (aeval x (pderiv j P) * D (x j)) + aeval x P * (aeval x (pderiv j (X n : MvPolynomial (Fin d) R)) * D (x j)) := by
        intro j
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, aeval_X]
        ring
      rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum]
      congr 2
      rw [Finset.sum_eq_single n]
      · simp
      · intro j _ hj; rw [pderiv_X_of_ne (Ne.symm hj)]; simp
      · simp
    rw [hs, map_mul, aeval_X, hD, hP]; ring
end ReciprocityTheory.PGsh
