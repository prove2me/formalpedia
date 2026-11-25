-- Prove2me | solution 1 for SpectralRepresentation.exists_continuousLinearMap_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:05:08.038051+00:00
-- url     : https://prove2.me/submissions/0a503e92-2697-4bc2-8876-7247793d750a

module
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Definitions.Def_BasicResults_Spectral_MonotoneConvergence
public import Theorems.Thm_SpectralRepresentation_norm_apply_sq_le_of_isPositive
public import Theorems.Thm_SpectralRepresentation_reApplyInnerSelf_mono
public import Theorems.Thm_SpectralRepresentation_exists_tendsto_of_antitone_isPositive

set_option autoImplicit true
@[expose] public section
public section
open ContinuousLinearMap RCLike
open scoped InnerProductSpace
open SpectralRepresentation
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Nontrivial H]
open Filter Topology
namespace SpectralRepresentation
theorem _root_.solution {T : ℕ → (H →L[ℂ] H)}
    (hpos : ∀ n, (T n).IsPositive) (hanti : Antitone T) :
    ∃ E : H →L[ℂ] H, ∀ x, Tendsto (fun n => T n x) atTop (𝓝 (E x)) := by
  have hbnd : ∀ k, ‖T k‖ ≤ ‖T 0‖ := fun k => by
    have hle : ‖T k‖ ≤ Real.sqrt (‖T k‖ * ‖T 0‖) := by
      refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun y => ?_
      have h1 : ‖T k y‖ ^ 2 ≤ ‖T k‖ * RCLike.re (⟪T k y, y⟫_ℂ) := norm_apply_sq_le_of_isPositive (hpos k) y
      have h2 : RCLike.re (⟪T k y, y⟫_ℂ) ≤ RCLike.re (⟪T 0 y, y⟫_ℂ) := by
        simpa only [ContinuousLinearMap.reApplyInnerSelf_apply] using reApplyInnerSelf_mono (hanti (Nat.zero_le k)) y
      have h3 : RCLike.re (⟪T 0 y, y⟫_ℂ) ≤ ‖T 0‖ * ‖y‖ ^ 2 := by
        calc RCLike.re (⟪T 0 y, y⟫_ℂ) ≤ ‖⟪T 0 y, y⟫_ℂ‖ := RCLike.re_le_norm _
          _ ≤ ‖T 0 y‖ * ‖y‖ := norm_inner_le_norm _ _
          _ ≤ (‖T 0‖ * ‖y‖) * ‖y‖ := mul_le_mul_of_nonneg_right ((T 0).le_opNorm y) (norm_nonneg y)
          _ = ‖T 0‖ * ‖y‖ ^ 2 := by ring
      have h4 : ‖T k y‖ ^ 2 ≤ (Real.sqrt (‖T k‖ * ‖T 0‖) * ‖y‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
        calc ‖T k y‖ ^ 2 ≤ ‖T k‖ * RCLike.re (⟪T k y, y⟫_ℂ) := h1
          _ ≤ ‖T k‖ * RCLike.re (⟪T 0 y, y⟫_ℂ) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
          _ ≤ ‖T k‖ * (‖T 0‖ * ‖y‖ ^ 2) := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
          _ = ‖T k‖ * ‖T 0‖ * ‖y‖ ^ 2 := by ring
      by_contra hlt
      push Not at hlt
      have hnn : 0 ≤ Real.sqrt (‖T k‖ * ‖T 0‖) * ‖y‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg y)
      nlinarith [norm_nonneg (T k y)]
    have hsq : ‖T k‖ ^ 2 ≤ ‖T k‖ * ‖T 0‖ := by
      have := mul_self_le_mul_self (norm_nonneg _) hle
      rwa [← sq, Real.mul_self_sqrt (mul_nonneg (norm_nonneg _) (norm_nonneg _))] at this
    by_cases h0 : ‖T k‖ = 0
    · rw [h0]; exact norm_nonneg _
    · exact le_of_mul_le_mul_left (by nlinarith) (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))
  choose e he using fun x => exists_tendsto_of_antitone_isPositive hpos hanti x
  let L : H →ₗ[ℂ] H :=
    { toFun := e
      map_add' := fun x y => by
        refine tendsto_nhds_unique (he (x + y)) ?_
        have h : (fun n => T n (x + y)) = (fun n => T n x + T n y) :=
          funext fun n => map_add (T n) x y
        rw [h]; exact (he x).add (he y)
      map_smul' := fun c x => by
        refine tendsto_nhds_unique (he (c • x)) ?_
        have h : (fun n => T n (c • x)) = (fun n => c • T n x) :=
          funext fun n => map_smul (T n) c x
        rw [h]; exact (he x).const_smul c }
  refine ⟨L.mkContinuous ‖T 0‖ fun x => ?_, fun x => he x⟩
  refine le_of_tendsto' (he x).norm fun n => ?_
  exact (T n).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hbnd n) (norm_nonneg x))
end SpectralRepresentation
