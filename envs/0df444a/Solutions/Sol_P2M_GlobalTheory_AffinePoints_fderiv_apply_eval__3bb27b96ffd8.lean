-- Prove2me | solution 1 for P2M_GlobalTheory_AffinePoints_fderiv_apply_eval__3bb27b96ffd8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:49:57.979804+00:00
-- url     : https://prove2.me/submissions/25b82d19-4883-42ef-abf0-faaf57287879

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AffinePoints_fderiv_apply_mul
import Theorems.Thm_GlobalTheory_AffinePoints_fderiv_apply_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial MeasureTheory Module
open scoped Manifold ContDiff
variable {A : Type} [CommRing A] [Algebra ℂ A] {d : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} {φ : E → (A →ₐ[ℂ] ℂ)}
namespace GlobalTheory.AffinePoints
theorem _root_.solution {R : Type*} [CommRing R] (g : R →+* A) {z : E}
    (hφ : ∀ a, DifferentiableAt ℂ (fun z => φ z a) z) (v : E)
    (hv : ∀ r, fderiv ℂ (fun z => φ z (g r)) z v = 0) (a : A) (h : Polynomial R) :
    fderiv ℂ (fun z => φ z (h.eval₂ g a)) z v =
      φ z ((Polynomial.derivative h).eval₂ g a) * fderiv ℂ (fun z => φ z a) z v := by
  induction h using Polynomial.induction_on with
  | C r => simpa using hv r
  | add P Q hP hQ =>
    rw [Polynomial.eval₂_add, fderiv_apply_add hφ, hP, hQ]
    simp [add_mul]
  | monomial n r ih =>
    rw [pow_succ, ← mul_assoc, Polynomial.eval₂_mul, Polynomial.eval₂_X, fderiv_apply_mul hφ, ih,
      Polynomial.derivative_mul (g := Polynomial.X), Polynomial.derivative_X, Polynomial.eval₂_add,
      Polynomial.eval₂_mul _ _ (p := Polynomial.derivative _), Polynomial.eval₂_X, mul_one]
    simp only [map_add, map_mul]
    ring
end GlobalTheory.AffinePoints
