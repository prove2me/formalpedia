-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianFormComparison_re_quad_eq_3680ef59eee8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:15.778942+00:00
-- url     : https://prove2.me/submissions/b4348ddc-9fe1-4de0-826c-38ca7c0dd676

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
open scoped ComplexOrder
open GroundTheory.Heights₂.Heights.HermitianFormComparison
namespace GroundTheory.Heights₂.Heights.HermitianFormComparison
theorem _root_.solution {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (x : Fin n → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).re = ∑ k, hA.eigenvalues k *
      ‖(star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ x) k‖ ^ 2 := by
  set U : Matrix (Fin n) (Fin n) ℂ := (↑hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  have hspec : A = U * diagonal (fun k => (hA.eigenvalues k : ℂ)) * star U := by
    have h := hA.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at h
    exact h
  set y : Fin n → ℂ := star U *ᵥ x with hy
  have hq : star x ⬝ᵥ (A *ᵥ x) = star y ⬝ᵥ (diagonal (fun k => (hA.eigenvalues k : ℂ)) *ᵥ y) := by
    conv_lhs => rw [hspec]
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, hy, star_mulVec,
      star_eq_conjTranspose U, conjTranspose_conjTranspose]
  rw [hq]
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re]
end GroundTheory.Heights₂.Heights.HermitianFormComparison
