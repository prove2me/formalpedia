-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.hessC_posSemidef_of_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:21:28.922366+00:00
-- url     : https://prove2.me/submissions/6caeea60-3162-4a2e-9e59-3bbbd21e7108

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureA
import Theorems.Thm_ReciprocityTheory_AnForm_M_leviC_conj_of_symm
import Theorems.Thm_ReciprocityTheory_AnForm_M_leviC_self_of_symm
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
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Complex
open scoped ContDiff ComplexOrder Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {e : ℕ} (f : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ)
    (hf : ContDiffAt ℝ 2 f z) (hl : ∀ w, 0 ≤ levi f z w) : (hessC f z).PosSemidef := by
  have hH := hf.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have hs : ∀ v w, fderiv ℝ (fderiv ℝ f) z v w = fderiv ℝ (fderiv ℝ f) z w v := fun v w => hH v w
  have hM : ∀ i j, hessC f z i j =
      leviC (fderiv ℝ (fderiv ℝ f) z) (Pi.single i 1) (Pi.single j 1) := hessC_eq_leviC f z
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.IsHermitian.ext fun i j => ?_) fun x => ?_
  · rw [hM, hM]
    exact leviC_conj_of_symm _ hs _ _
  · have h1 : ∀ i, ∑ j, hessC f z i j * x j =
        leviC (fderiv ℝ (fderiv ℝ f) z) (Pi.single i 1) (star x) := by
      intro i
      rw [← leviC_conj_of_symm _ hs (star x) (Pi.single i 1),
        ← sum_mul_leviC (fderiv ℝ (fderiv ℝ f) z) (star x) (Pi.single i 1), map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hM, map_mul, leviC_conj_of_symm _ hs]
      simp [mul_comm]
    have h2 : star x ⬝ᵥ (hessC f z *ᵥ x) =
        leviC (fderiv ℝ (fderiv ℝ f) z) (star x) (star x) := by
      rw [← sum_mul_leviC (fderiv ℝ (fderiv ℝ f) z) (star x) (star x)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← h1 i]
      rfl
    rw [h2, leviC_self_of_symm _ hs]
    exact_mod_cast hl (star x)
end ReciprocityTheory.AnForm.M
