-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TubeFormComparison_levi_neg_eba6193b69bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:22:57.875394+00:00
-- url     : https://prove2.me/submissions/1a72c863-6153-480e-8293-91277208ef54

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeFormCompare

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
theorem _root_.solution {N : ℕ} (φ : (Fin N → ℂ) → ℝ) (z w : Fin N → ℂ) :
    levi (fun y => -φ y) z w = -levi φ z w := by
  have h1 : fderiv ℝ (fun y => -φ y) = -(fderiv ℝ φ) := funext fun y => fderiv_neg
  unfold levi
  rw [h1, fderiv_neg]
  simp only [_root_.neg_apply]
  ring
end GroundTheory.Heights₂.Heights.TubeFormComparison
