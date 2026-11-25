-- Prove2me | solution 1 for PI.LocCartanPair.splPlane_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:57:36.284876+00:00
-- url     : https://prove2.me/submissions/effe476a-94d1-4b3c-880f-4d7744f5336c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_SplPlane
import Theorems.Thm_PI_LocCartanPair_splPlane_herm
import Theorems.Thm_PI_LocCartanPair_splPlane_unitEntry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.LocCartanPair
variable {R : Type} [CommRing R] [StarRing R]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {R : Type} [CommRing R] [StarRing R]
namespace PI.LocCartanPair
theorem _root_.solution [IsLocalRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R)
    (hA : Aᴴ = A) (x y : ι → R) (hxx : star x ⬝ᵥ (A *ᵥ x) = 0)
    (hxy : star x ⬝ᵥ (A *ᵥ y) = 1) :
    ∃ i₀ j₀, i₀ ≠ j₀ ∧ IsUnit (x i₀ * y j₀ - y i₀ * x j₀) := by
  have hyx : star y ⬝ᵥ (A *ᵥ x) = 1 := by rw [← splPlane_herm A hA x y, hxy, star_one]
  rw [dotProduct_mulVec] at hyx
  obtain ⟨i₀, hi₀⟩ := splPlane_unitEntry _ _ hyx
  obtain ⟨xi, hxi⟩ := hi₀.exists_right_inv
  set y' := y - (y i₀ * xi) • x with hy'
  have hy'i : y' i₀ = 0 := by
    simp only [hy', Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(y i₀)) * hxi
  have hxy' : (star x ᵥ* A) ⬝ᵥ y' = 1 := by
    rw [← dotProduct_mulVec, hy', mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hxx,
      hxy, smul_eq_mul, mul_zero, sub_zero]
  obtain ⟨j₀, hj₀⟩ := splPlane_unitEntry _ _ hxy'
  have hne : i₀ ≠ j₀ := by
    rintro rfl; rw [hy'i] at hj₀; exact not_isUnit_zero hj₀
  refine ⟨i₀, j₀, hne, ?_⟩
  have e : x i₀ * y j₀ - y i₀ * x j₀ = x i₀ * y' j₀ := by
    simp only [hy', Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (y i₀ * x j₀) * hxi
  rw [e]; exact hi₀.mul hj₀
end PI.LocCartanPair
