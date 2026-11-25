-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.pushA_detR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:07:03.738336+00:00
-- url     : https://prove2.me/submissions/f642c82c-1a0e-4a97-9dce-900f5163878f

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter
import Theorems.Thm_ReciprocityTheory_AnForm_A_det_restrictScalars_real


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
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (f : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :
    (f.restrictScalars ℝ).det = Complex.normSq (LinearMap.det (f : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) :=
  ReciprocityTheory.AnForm.A.det_restrictScalars_real (f : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))
end ReciprocityTheory.AnForm.M
