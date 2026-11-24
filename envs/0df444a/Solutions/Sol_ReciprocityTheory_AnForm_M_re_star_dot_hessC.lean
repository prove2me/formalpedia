-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.re_star_dot_hessC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:55.603188+00:00
-- url     : https://prove2.me/submissions/c9edb64f-d98a-45a0-be97-3a5ea986d83f

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_hessC_eq_lv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff ComplexOrder Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {D : ℕ} (φ : (Fin D → ℂ) → ℝ) (z x : Fin D → ℂ) :
    (star x ⬝ᵥ (hessC φ z *ᵥ x)).re = levi φ z (star x) := by
  classical
  obtain ⟨H, hH⟩ : ∃ H, H = fderiv ℝ (fderiv ℝ φ) z := ⟨_, rfl⟩
  let E : Fin D → Fin D → ℂ := fun i => Pi.single i 1

  have hw : star x = ∑ i, ((x i).re • E i + (-(x i).im) • (Complex.I • E i)) := by
    ext k
    rw [Finset.sum_apply, Finset.sum_eq_single k
      (fun i _ hik => by simp [E, Pi.single_apply, hik.symm]) (by simp)]
    simp [E, Complex.ext_iff]
  have hIw : Complex.I • star x = ∑ i, ((x i).im • E i + (x i).re • (Complex.I • E i)) := by
    ext k
    rw [Finset.sum_apply, Finset.sum_eq_single k
      (fun i _ hik => by simp [E, Pi.single_apply, hik.symm]) (by simp)]
    simp [E, Complex.ext_iff]
  have hL : (star x ⬝ᵥ (hessC φ z *ᵥ x)).re = ∑ i, ∑ j,
      (((x i).re * (x j).re + (x i).im * (x j).im) *
          (H (E i) (E j) + H (Complex.I • E i) (Complex.I • E j)) +
        ((x i).im * (x j).re - (x i).re * (x j).im) *
          (H (E i) (Complex.I • E j) - H (Complex.I • E i) (E j))) / 4 := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [ReciprocityTheory.AnForm.A.TraceConjugationCover.hessC_eq_lv, ← hH]
    simp [ReciprocityTheory.AnForm.A.TraceConjugationCover.lv, E, Complex.mul_re, Complex.mul_im]
    ring
  have hR : levi φ z (star x) = ∑ i, ∑ j,
      (((x i).re * (x j).re + (x i).im * (x j).im) *
          (H (E i) (E j) + H (Complex.I • E i) (Complex.I • E j)) +
        ((x i).im * (x j).re - (x i).re * (x j).im) *
          (H (E i) (Complex.I • E j) - H (Complex.I • E i) (E j))) / 4 := by
    unfold levi
    rw [← hH, hIw, hw]
    simp only [map_sum, map_add, map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, smul_eq_mul]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hL, hR]
end ReciprocityTheory.AnForm.M
