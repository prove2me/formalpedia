-- Prove2me | solution 1 for SpectralRepresentation.exists_tendsto_of_antitone_isPositive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:04:05.482344+00:00
-- url     : https://prove2.me/submissions/4381fa96-ce5d-41e8-9a9e-133047b5946e

module
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Definitions.Def_BasicResults_Spectral_MonotoneConvergence
public import Theorems.Thm_SpectralRepresentation_norm_apply_sq_le_of_isPositive
public import Theorems.Thm_SpectralRepresentation_reApplyInnerSelf_mono
section
@[expose] public section
open ContinuousLinearMap RCLike
open scoped InnerProductSpace
namespace SpectralRepresentation
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Nontrivial H]
open Filter Topology in
omit [CompleteSpace H] [Nontrivial H] in
/-- `re⟪(B - C) x, x⟫` splits additively over the difference. -/
private theorem reApplyInnerSelf_sub (B C : H →L[ℂ] H) (x : H) :
    (B - C).reApplyInnerSelf x = B.reApplyInnerSelf x - C.reApplyInnerSelf x := by
  simp only [ContinuousLinearMap.reApplyInnerSelf_apply, sub_apply,
    inner_sub_left, map_sub]
end SpectralRepresentation
end
end

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
    (hpos : ∀ n, (T n).IsPositive) (hanti : Antitone T) (x : H) :
    ∃ y, Tendsto (fun n => T n x) atTop (𝓝 y) := by
  set a : ℕ → ℝ := fun n => (T n).reApplyInnerSelf x with ha_def
  have ha_anti : Antitone a := fun m n hmn => reApplyInnerSelf_mono (hanti hmn) x
  have ha_bdd : BddBelow (Set.range a) := ⟨0, by rintro _ ⟨n, rfl⟩; exact (hpos n).2 x⟩
  set L : ℝ := ⨅ n, a n with hL_def
  have ha_tendsto : Tendsto a atTop (𝓝 L) := tendsto_atTop_ciInf ha_anti ha_bdd
  have hnorm_bound : ∀ m n, ‖T m - T n‖ ≤ 2 * ‖T 0‖ := by
    intro m n
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
    calc ‖T m - T n‖ ≤ ‖T m‖ + ‖T n‖ := norm_sub_le _ _
      _ ≤ ‖T 0‖ + ‖T 0‖ := by gcongr <;> exact hbnd _
      _ = 2 * ‖T 0‖ := by ring
  have key : ∀ m n, n ≤ m → ‖T m x - T n x‖ ^ 2 ≤ 2 * ‖T 0‖ * (a n - a m) := by
    intro m n hnm
    have hpmn : (T n - T m).IsPositive := hanti hnm
    have h1 : ‖T m x - T n x‖ = ‖(T n - T m) x‖ := by
      rw [sub_apply]; exact norm_sub_rev _ _
    rw [h1]
    calc ‖(T n - T m) x‖ ^ 2
        ≤ ‖T n - T m‖ * RCLike.re (⟪(T n - T m) x, x⟫_ℂ) :=
          norm_apply_sq_le_of_isPositive hpmn x
      _ = ‖T n - T m‖ * (a n - a m) := by
          rw [← ContinuousLinearMap.reApplyInnerSelf_apply, reApplyInnerSelf_sub]
      _ ≤ 2 * ‖T 0‖ * (a n - a m) :=
          mul_le_mul_of_nonneg_right (hnorm_bound n m) (sub_nonneg.mpr (ha_anti hnm))
  have hCauchy : CauchySeq (fun n => T n x) := by
    refine cauchySeq_of_le_tendsto_0 (fun N => Real.sqrt (2 * ‖T 0‖ * (a N - L))) ?_ ?_
    · intro n m N hNn hNm
      have hbound : ∀ i j, j ≤ i → N ≤ j → ‖T i x - T j x‖ ^ 2 ≤ 2 * ‖T 0‖ * (a N - L) := by
        intro i j hji hNj
        refine (key i j hji).trans ?_
        have hj : a j ≤ a N := ha_anti hNj
        have hi : L ≤ a i := ciInf_le ha_bdd i
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg (T n x - T m x))]
      apply Real.sqrt_le_sqrt
      rcases le_total m n with hmn | hnm
      · exact hbound n m hmn hNm
      · rw [show ‖T n x - T m x‖ = ‖T m x - T n x‖ from norm_sub_rev _ _]
        exact hbound m n hnm hNn
    · have h0 : Tendsto (fun N => 2 * ‖T 0‖ * (a N - L)) atTop (𝓝 0) := by
        have : Tendsto (fun N => a N - L) atTop (𝓝 0) := by simpa using ha_tendsto.sub_const L
        simpa using this.const_mul (2 * ‖T 0‖)
      have hsqrt := (Real.continuous_sqrt.tendsto 0).comp h0
      rw [Real.sqrt_zero] at hsqrt
      exact hsqrt
  exact cauchySeq_tendsto_of_complete hCauchy
end SpectralRepresentation
