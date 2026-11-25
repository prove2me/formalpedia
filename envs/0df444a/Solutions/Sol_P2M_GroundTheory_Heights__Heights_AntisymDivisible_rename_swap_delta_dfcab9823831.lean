-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AntisymDivisible_rename_swap_delta_dfcab9823831
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:43:47.8049+00:00
-- url     : https://prove2.me/submissions/9100b8ae-9a0a-417e-9641-e06833fa5d30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymDivisible
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_swap_pair_f5c9f49b9aee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_delta_factor_eq_det_6686b3b8ba3c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.AntisymDivisible
variable {T : Type} [Fintype T] [DecidableEq T] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.AntisymDivisible
theorem _root_.solution (τ₀ : T) {a b : Fin N} (hab : a ≠ b) :
    rename (Equiv.swap (τ₀, a) (τ₀, b)) (antisymDelta T N) = -antisymDelta T N := by
  have key : ∀ τ, rename (R := ℝ) (Equiv.swap (τ₀, a) (τ₀, b))
      (Matrix.vandermonde (fun i : Fin N => (-X (τ, i) : MvPolynomial (T × Fin N) ℝ))).det =
      (if τ = τ₀ then -1 else 1) *
        (Matrix.vandermonde (fun i : Fin N => (-X (τ, i) : MvPolynomial (T × Fin N) ℝ))).det := by
    intro τ
    rw [AlgHom.map_det]
    by_cases hτ : τ = τ₀
    · subst hτ
      have : (rename (R := ℝ) (Equiv.swap (τ, a) (τ, b))).mapMatrix
          (Matrix.vandermonde (fun i : Fin N => (-X (τ, i) : MvPolynomial (T × Fin N) ℝ))) =
          (Matrix.vandermonde (fun i : Fin N => (-X (τ, i) : MvPolynomial (T × Fin N) ℝ))).submatrix
            (Equiv.swap a b) id := by
        ext i k
        simp [Matrix.vandermonde_apply, swap_pair]
      rw [this, Matrix.det_permute, Equiv.Perm.sign_swap hab]
      simp
    · have : (rename (R := ℝ) (Equiv.swap (τ₀, a) (τ₀, b))).mapMatrix
          (Matrix.vandermonde (fun i : Fin N => (-X (τ, i) : MvPolynomial (T × Fin N) ℝ))) =
          Matrix.vandermonde (fun i : Fin N => (-X (τ, i) : MvPolynomial (T × Fin N) ℝ)) := by
        ext i k
        simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.vandermonde_apply, map_pow,
          map_neg, rename_X]
        rw [Equiv.swap_apply_of_ne_of_ne (by simp [hτ]) (by simp [hτ])]
      rw [this, if_neg hτ, one_mul]
  unfold antisymDelta
  simp_rw [delta_factor_eq_det]
  rw [map_prod]
  simp_rw [key]
  rw [Finset.prod_mul_distrib]
  simp [Finset.prod_ite_eq']
end GroundTheory.Heights₂.Heights.AntisymDivisible
