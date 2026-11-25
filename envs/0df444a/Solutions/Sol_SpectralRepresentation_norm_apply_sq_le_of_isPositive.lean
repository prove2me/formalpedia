-- Prove2me | solution 1 for SpectralRepresentation.norm_apply_sq_le_of_isPositive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:03:18.639348+00:00
-- url     : https://prove2.me/submissions/72949813-aa5d-413a-add3-0d45d41684b7

module
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Definitions.Def_BasicResults_Spectral_MonotoneConvergence
public import Theorems.Thm_SpectralRepresentation_sq_le_norm_smul_of_isPositive

set_option autoImplicit true
@[expose] public section
public section
open ContinuousLinearMap RCLike
open scoped InnerProductSpace
open SpectralRepresentation
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Nontrivial H]
namespace SpectralRepresentation
theorem _root_.solution {A : H →L[ℂ] H} (hA : A.IsPositive) (x : H) :
    ‖A x‖ ^ 2 ≤ ‖A‖ * RCLike.re (⟪A x, x⟫_ℂ) := by
  have hsa : adjoint A = A := hA.isSelfAdjoint
  -- `‖A x‖² = re ⟪A² x, x⟫`.
  have hAsq : RCLike.re (⟪(A ^ 2) x, x⟫_ℂ) = ‖A x‖ ^ 2 := by
    rw [pow_two, mul_apply_eq_comp,
      ← ContinuousLinearMap.adjoint_inner_right A (A x) x, hsa, inner_self_eq_norm_sq]
  -- Monotonicity of `re⟪· x, x⟫` from `A² ≤ ‖A‖ • A`.
  have hpos : ((‖A‖ : ℝ) • A - A ^ 2).IsPositive := sq_le_norm_smul_of_isPositive hA
  have hmono : RCLike.re (⟪(A ^ 2) x, x⟫_ℂ) ≤ RCLike.re (⟪((‖A‖ : ℝ) • A) x, x⟫_ℂ) := by
    have h0 := hpos.2 x
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, sub_apply,
      inner_sub_left, map_sub, sub_nonneg] at h0
    exact h0
  -- `re⟪(‖A‖ • A) x, x⟫ = ‖A‖ · re⟪A x, x⟫`.
  have hsmul : RCLike.re (⟪((‖A‖ : ℝ) • A) x, x⟫_ℂ) = ‖A‖ * RCLike.re (⟪A x, x⟫_ℂ) := by
    rw [smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ),
      inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul]
  rw [← hAsq]
  exact hmono.trans_eq hsmul
end SpectralRepresentation
