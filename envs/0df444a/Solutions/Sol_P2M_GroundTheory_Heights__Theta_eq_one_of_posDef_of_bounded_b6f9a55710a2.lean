-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_eq_one_of_posDef_of_bounded_b6f9a55710a2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:44:37.304393+00:00
-- url     : https://prove2.me/submissions/b15387ff-a9a6-4b54-b62c-903496f7e19e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsPolar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Cartan
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conjCME_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightDerivEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] GroundTheory.Automorphic.conjCME_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {p q : ℕ}
local notation "𝔐" => Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ
local notation "J" => indefJ p q
local notation "G" => indefiniteUnitaryGroup p q
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℂ} (hP : P.PosDef) {C : ℝ} (h1 : ∀ k : ℕ, ‖P ^ k‖ ≤ C)
    (h2 : ∀ k : ℕ, ‖P⁻¹ ^ k‖ ≤ C) : P = 1 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · ext i; exact isEmptyElim i
  have hH := hP.isHermitian
  have hu : IsUnit P := hP.isUnit
  have hle : ∀ A : Matrix n n ℂ, (∀ k : ℕ, ‖A ^ k‖ ≤ C) → ∀ z ∈ spectrum ℂ A, ‖z‖ ≤ 1 := by
    intro A hA z hz
    by_contra hlt
    push Not at hlt
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (C * ‖(1 : Matrix n n ℂ)‖) hlt
    have h := spectrum.norm_le_norm_mul_of_mem (spectrum.pow_mem_pow A k hz)
    rw [norm_pow] at h
    have h1n : 0 ≤ ‖(1 : Matrix n n ℂ)‖ := norm_nonneg _
    nlinarith [hA k]
  have key : ∀ i, hH.eigenvalues i = 1 := by
    intro i
    set t := hH.eigenvalues i
    have ht : 0 < t := hP.eigenvalues_pos i
    have hmem : (t : ℂ) ∈ spectrum ℂ P := by
      rw [hH.spectrum_eq_image_range]
      exact ⟨t, ⟨i, rfl⟩, rfl⟩
    have hmem' : (t : ℂ)⁻¹ ∈ spectrum ℂ P⁻¹ := by
      have := (spectrum.inv₀_mem_iff (r := (t : ℂ)⁻¹) (a := hu.unit)).1
        (by rw [inv_inv, IsUnit.unit_spec]; exact hmem)
      rwa [Matrix.coe_units_inv, IsUnit.unit_spec] at this
    have a1 := hle P h1 _ hmem
    have a2 := hle P⁻¹ h2 _ hmem'
    rw [Complex.norm_real, Real.norm_of_nonneg ht.le] at a1
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg ht.le, inv_le_one₀ ht] at a2
    linarith
  rw [hH.spectral_theorem]
  have : (RCLike.ofReal ∘ hH.eigenvalues : n → ℂ) = 1 := by
    funext i
    simp [key i]
  rw [this, Pi.one_def, diagonal_one, map_one]
end GroundTheory.Heights₂.Theta
