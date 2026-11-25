-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TubeFormComparison_levi_eq_re_bde4222f82b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:21:21.130461+00:00
-- url     : https://prove2.me/submissions/5be3976d-c67c-4fda-83cb-200313f06a8b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeFormCompare
import Theorems.Thm_ReciprocityTheory_AnForm_M_sum_leviC_right
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
open MvPolynomial Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.TubeFormComparison
namespace GroundTheory.Heights₂.Heights.TubeFormComparison
theorem _root_.solution {N : ℕ} (φ : (Fin N → ℂ) → ℝ) (z a : Fin N → ℂ) :
    levi φ z a = (a ⬝ᵥ (hessC φ z *ᵥ star a)).re := by
  have hq : star (star a) ⬝ᵥ (hessC φ z *ᵥ star a) =
      leviC (fderiv ℝ (fderiv ℝ φ) z) (star (star a)) (star (star a)) := by
    rw [Matrix.dotProduct_mulVec]
    simp only [Matrix.vecMul, dotProduct, hessC_eq_leviC, sum_mul_leviC]
    exact ReciprocityTheory.AnForm.M.sum_leviC_right _ _ _
  rw [star_star] at hq
  rw [hq]
  simp [leviC, levi]
end GroundTheory.Heights₂.Heights.TubeFormComparison
