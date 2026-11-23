-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.maDens_congr_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:47.045506+00:00
-- url     : https://prove2.me/submissions/12deaadb-ebf3-44aa-b3bf-632a0eadb4ac

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Pullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : ∀ i, φ i =ᶠ[𝓝 y] ψ i) : maDens φ y = maDens ψ y := by
  have hH : ∀ i, hessC (φ i) y = hessC (ψ i) y := by
    intro i
    have h2 : fderiv ℝ (fderiv ℝ (φ i)) y = fderiv ℝ (fderiv ℝ (ψ i)) y := (h i).fderiv.fderiv_eq
    unfold hessC
    simp only [h2]
    rfl
  simp only [maDens, hH]
end ReciprocityTheory.AnForm.M
