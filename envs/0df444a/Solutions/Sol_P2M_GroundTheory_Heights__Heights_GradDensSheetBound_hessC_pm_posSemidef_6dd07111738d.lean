-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GradDensSheetBound_hessC_pm_posSemidef_6dd07111738d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:21:18.956948+00:00
-- url     : https://prove2.me/submissions/fd77f150-5a2d-4303-8b9a-c8bb5f25000b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGradDensSheetBound
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_isHermitian
import Theorems.Thm_ReciprocityTheory_AnForm_A_sum_leviC_mul
import Theorems.Thm_ReciprocityTheory_AnForm_hessC_eq_leviC
import Theorems.Thm_ReciprocityTheory_AnForm_sum_mul_leviC


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
open ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.GradDensSheetBound
namespace GroundTheory.Heights₂.Heights.GradDensSheetBound
theorem _root_.solution {e : ℕ} (φ : (Fin e → ℂ) → ℝ) (x : Fin e → ℂ)
    (h2 : ContDiffAt ℝ 2 φ x) (M c : ℝ) (hM : ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ M) (hc : M / 2 ≤ c) :
    ((c : ℂ) • (1 : Matrix (Fin e) (Fin e) ℂ) - hessC φ x).PosSemidef ∧
      (hessC φ x + (c : ℂ) • (1 : Matrix (Fin e) (Fin e) ℂ)).PosSemidef := by
  have hs : IsSymmSndFDerivAt ℝ φ x := h2.isSymmSndFDerivAt (by simp)
  have hH := hessC_isHermitian φ x h2
  have hM0 : 0 ≤ M := (ContinuousLinearMap.opNorm_nonneg _).trans hM
  have hI : ((c : ℂ) • (1 : Matrix (Fin e) (Fin e) ℂ)).IsHermitian := by
    simp [IsHermitian, conjTranspose_smul]
  have hq : ∀ ξ : Fin e → ℂ, (star ξ ⬝ᵥ (hessC φ x *ᵥ ξ)).im = 0 ∧
      |(star ξ ⬝ᵥ (hessC φ x *ᵥ ξ)).re| ≤ c * ∑ j, ‖ξ j‖ ^ 2 := by
    intro ξ
    set H := fderiv ℝ (fderiv ℝ φ) x with hHdef
    have key : star ξ ⬝ᵥ (hessC φ x *ᵥ ξ) = leviC H (star ξ) (star ξ) := by
      simp only [dotProduct, mulVec, hessC_eq_leviC, sum_leviC_mul]
      exact sum_mul_leviC _ (star ξ) (star ξ)
    rw [key]
    refine ⟨by simp only [leviC, hHdef]; rw [hs (star ξ) (Complex.I • star ξ)]; simp, ?_⟩
    have hre : (leviC H (star ξ) (star ξ)).re =
        (H (star ξ) (star ξ) + H (Complex.I • star ξ) (Complex.I • star ξ)) / 4 := by
      simp [leviC]
    have hn : ‖star ξ‖ ^ 2 ≤ ∑ j, ‖ξ j‖ ^ 2 := by
      have hle : ‖star ξ‖ ≤ Real.sqrt (∑ j, ‖ξ j‖ ^ 2) := by
        refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
        rw [Pi.star_apply, norm_star]
        exact Real.le_sqrt_of_sq_le (Finset.single_le_sum (f := fun j => ‖ξ j‖ ^ 2)
          (fun j _ => by positivity) (Finset.mem_univ j))
      calc ‖star ξ‖ ^ 2 ≤ Real.sqrt (∑ j, ‖ξ j‖ ^ 2) ^ 2 := by gcongr
        _ = _ := Real.sq_sqrt (by positivity)
    have hIa : ‖Complex.I • star ξ‖ = ‖star ξ‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    have h1 : |H (star ξ) (star ξ)| ≤ M * ‖star ξ‖ ^ 2 := by
      have := H.le_opNorm₂ (star ξ) (star ξ)
      rw [Real.norm_eq_abs] at this
      nlinarith [mul_le_mul_of_nonneg_right hM (sq_nonneg ‖star ξ‖)]
    have h2 : |H (Complex.I • star ξ) (Complex.I • star ξ)| ≤ M * ‖star ξ‖ ^ 2 := by
      have := H.le_opNorm₂ (Complex.I • star ξ) (Complex.I • star ξ)
      rw [Real.norm_eq_abs, hIa] at this
      nlinarith [mul_le_mul_of_nonneg_right hM (sq_nonneg ‖star ξ‖)]
    rw [hre, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4), div_le_iff₀ (by norm_num)]
    have h3 := abs_add_le (H (star ξ) (star ξ)) (H (Complex.I • star ξ) (Complex.I • star ξ))
    nlinarith [mul_le_mul_of_nonneg_left hn hM0, mul_le_mul_of_nonneg_right hc
      (Finset.sum_nonneg (fun j _ => sq_nonneg ‖ξ j‖) : 0 ≤ ∑ j, ‖ξ j‖ ^ 2)]
  have hval : ∀ ξ : Fin e → ℂ, star ξ ⬝ᵥ (((c : ℂ) • (1 : Matrix (Fin e) (Fin e) ℂ)) *ᵥ ξ) =
      ((c * ∑ j, ‖ξ j‖ ^ 2 : ℝ) : ℂ) := by
    intro ξ
    have hmv : ((c : ℂ) • (1 : Matrix (Fin e) (Fin e) ℂ)) *ᵥ ξ = (c : ℂ) • ξ := by
      ext j; simp [mulVec, dotProduct, Matrix.one_apply]
    rw [hmv, dotProduct_smul, smul_eq_mul]
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  constructor
  · refine PosSemidef.of_dotProduct_mulVec_nonneg (hI.sub hH) fun ξ => ?_
    obtain ⟨him, hre⟩ := hq ξ
    rw [sub_mulVec, dotProduct_sub, hval, Complex.nonneg_iff]
    refine ⟨?_, ?_⟩
    · simp only [Complex.sub_re, Complex.ofReal_re]
      linarith [(abs_le.1 hre).2]
    · rw [Complex.sub_im, Complex.ofReal_im, him]; norm_num
  · refine PosSemidef.of_dotProduct_mulVec_nonneg (hH.add hI) fun ξ => ?_
    obtain ⟨him, hre⟩ := hq ξ
    rw [add_mulVec, dotProduct_add, hval, Complex.nonneg_iff]
    refine ⟨?_, ?_⟩
    · simp only [Complex.add_re, Complex.ofReal_re]
      linarith [(abs_le.1 hre).1]
    · rw [Complex.add_im, Complex.ofReal_im, him]; norm_num
end GroundTheory.Heights₂.Heights.GradDensSheetBound
