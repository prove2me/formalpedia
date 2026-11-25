-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TubeFormComparison_hessC_neg_f4567154ff3b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:22:36.455802+00:00
-- url     : https://prove2.me/submissions/a32d4be2-72dc-4b51-b8c1-aebf9d1829fa

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeFormCompare
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_hessC_const_mul__03a5d330ff52


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
theorem _root_.solution {N : ℕ} (φ : (Fin N → ℂ) → ℝ) (z : Fin N → ℂ) :
    hessC (fun y => -φ y) z = -hessC φ z := by
  have h : (fun y => -φ y) = fun y => (-1 : ℝ) * φ y := funext fun y => by ring
  rw [h, ReciprocityTheory.AnForm.M.hessC_const_mul']
  simp
end GroundTheory.Heights₂.Heights.TubeFormComparison
