-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_hessC_congr_of_eventuallyEq_ccfec28cf87b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:56.736052+00:00
-- url     : https://prove2.me/submissions/69441f18-8218-4042-bb67-3a3e1892ae16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRankDropDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Pullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRankDropDens

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution {D : ℕ} {φ ψ : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : φ =ᶠ[𝓝 z] ψ) : ReciprocityTheory.AnForm.hessC φ z = ReciprocityTheory.AnForm.hessC ψ z := by
  have h1 : fderiv ℝ φ =ᶠ[𝓝 z] fderiv ℝ ψ := h.fderiv
  unfold ReciprocityTheory.AnForm.hessC
  rw [h1.fderiv_eq]
end GroundTheory.Heights₂.Heights.Targets
